// SPDX-License-Identifier: Apache-2.0

package chisel3.internal.plugin

import scala.collection.mutable
import scala.tools.nsc
import scala.tools.nsc.{Global, Phase}
import scala.tools.nsc.plugins.PluginComponent
import scala.tools.nsc.symtab.Flags
import scala.tools.nsc.transform.TypingTransformers

/** Performs three operations
  * 1) Records that this plugin ran on a bundle by adding a method
  *    `override protected def _usingPlugin: Boolean = true`
  * 2) Constructs a cloneType method
  * 3) Builds a `def elements` that is computed once in this plugin
  *    Eliminates needing reflection to discover the hardware fields of a `Bundle`
  *
  * @param global     the environment
  * @param arguments  run time parameters to code
  */
private[plugin] class BundleComponent(val global: Global, arguments: ChiselPluginArguments)
    extends PluginComponent
    with TypingTransformers {
  import global._

  val phaseName: String = "chiselbundlephase"
  val runsAfter: List[String] = "typer" :: Nil
  def newPhase(prev: Phase): Phase = new BundlePhase(prev)

  private class BundlePhase(prev: Phase) extends StdPhase(prev) {
    override def name: String = phaseName
    def apply(unit: CompilationUnit): Unit = {
      // This plugin doesn't work on Scala 2.11 nor Scala 3. Rather than complicate the sbt build flow,
      // instead we just check the version and if its an early Scala version, the plugin does nothing
      val scalaVersion = scala.util.Properties.versionNumberString.split('.')
      val scalaVersionOk = scalaVersion(0).toInt == 2 && scalaVersion(1).toInt >= 12
      if (scalaVersionOk && arguments.useBundlePlugin) {
        unit.body = new MyTypingTransformer(unit).transform(unit.body)
      } else {
        val reason = if (!scalaVersionOk) {
          s"invalid Scala version '${scala.util.Properties.versionNumberString}'"
        } else {
          s"not enabled via '${arguments.useBundlePluginFullOpt}'"
        }
        // Enable this with scalacOption '-Ylog:chiselbundlephase'
        global.log(s"Skipping BundleComponent on account of $reason.")
      }
    }
  }

  private class MyTypingTransformer(unit: CompilationUnit) extends TypingTransformer(unit) {

    def inferType(t: Tree): Type = localTyper.typed(t, nsc.Mode.TYPEmode).tpe

    val bundleTpe:         Type = inferType(tq"chisel3.Bundle")
    val dataTpe:           Type = inferType(tq"chisel3.Data")
    val genericSeq:        Type = inferType(tq"scala.collection.Seq[_]")
    val seqOfUIntTpe:      Type = inferType(tq"scala.collection.Seq[chisel3.UInt]")
    val seqOfDataTpe:      Type = inferType(tq"scala.collection.Seq[chisel3.Data]")
    val seqMapTpe:         Type = inferType(tq"scala.collection.immutable.SeqMap[String,Any]")
    val ignoreSeqInBundle: Type = inferType(tq"chisel3.IgnoreSeqInBundle")

    // Not cached because it should only be run once per class (thus once per Type)
    def isBundle(sym: Symbol): Boolean = { sym.tpe <:< bundleTpe }
    def isSeqOfData(sym: Symbol): Boolean = {
      println(s"IsSeqOfData: ${sym.tpe} ${sym.tpe.toString}")
      sym.tpe <:< seqOfDataTpe ||
      (sym.tpe.baseClasses.exists(t => t.tpe <:< dataTpe) &&
      sym.tpe.baseClasses.exists(t => t.tpe <:< genericSeq)) ||
      sym.tpe.toString.contains("Seq[chisel3")
    }
    def typeIsSeqOfData(tpe: Type): Boolean = {
      tpe.toString.contains("Seq[chisel3")
    }
    def typeIsOptionOfData(tpe: Type): Boolean = {
      tpe.toString.startsWith("=> Option[chisel3") ||
      tpe.toString.startsWith("Option[chisel3")
    }
    def isSeqOfUInt(sym: Symbol): Boolean = { sym.tpe <:< seqOfUIntTpe }
    def isExactBundle(sym: Symbol): Boolean = { sym.tpe =:= bundleTpe }
    def isIgnoreSeqInBundle(sym: Symbol): Boolean = { sym.tpe <:< ignoreSeqInBundle }

    // Cached because this is run on every argument to every Bundle
    val isDataCache = new mutable.HashMap[Type, Boolean]
    def isData(sym: Symbol): Boolean = isDataCache.getOrElseUpdate(sym.tpe, sym.tpe <:< dataTpe)

    def cloneTypeFull(tree: Tree): Tree =
      localTyper.typed(q"chisel3.experimental.DataMirror.internal.chiselTypeClone[${tree.tpe}]($tree)")

    def isNullaryMethodNamed(name: String, defdef: DefDef): Boolean =
      defdef.name.decodedName.toString == name && defdef.tparams.isEmpty && defdef.vparamss.isEmpty

    def getConstructorAndParams(body: List[Tree]): (Option[DefDef], Seq[Symbol]) = {
      val paramAccessors = mutable.ListBuffer[Symbol]()
      var primaryConstructor: Option[DefDef] = None
      body.foreach {
        case acc: ValDef if acc.symbol.isParamAccessor =>
          paramAccessors += acc.symbol
        case con: DefDef if con.symbol.isPrimaryConstructor =>
          primaryConstructor = Some(con)
        case d: DefDef if isNullaryMethodNamed("_cloneTypeImpl", d) =>
          val msg = "Users cannot override _cloneTypeImpl. Let the compiler plugin generate it."
          global.globalError(d.pos, msg)
        case d: DefDef if isNullaryMethodNamed("_usingPlugin", d) =>
          val msg = "Users cannot override _usingPlugin, it is for the compiler plugin's use only."
          global.globalError(d.pos, msg)
        case d: DefDef if isNullaryMethodNamed("cloneType", d) =>
          val msg = "Users cannot override cloneType.  Let the compiler plugin generate it."
          global.globalError(d.pos, msg)
        case _ =>
      }
      (primaryConstructor, paramAccessors.toList)
    }

    override def transform(tree: Tree): Tree = tree match {

      case bundle: ClassDef if isBundle(bundle.symbol) =>
        def show(string: => String): Unit = {
          if (
            !arguments.pluginDebugBundlePattern.isEmpty &&
            bundle.symbol.name.toString.matches(arguments.pluginDebugBundlePattern)
          ) {
            println(string)
          }
        }

        // ==================== Generate _cloneTypeImpl ====================
        val (con, params) = getConstructorAndParams(bundle.impl.body)
        if (con.isEmpty) {
          global.reporter.warning(bundle.pos, "Unable to determine primary constructor!")
          return super.transform(tree)
        }

        val constructor = con.get
        val thiz = gen.mkAttributedThis(bundle.symbol)

        // The params have spaces after them (Scalac implementation detail)
        val paramLookup: String => Symbol = params.map(sym => sym.name.toString.trim -> sym).toMap

        var additionalMethods: Seq[Tree] = Seq()

        if (!bundle.mods.hasFlag(Flag.ABSTRACT)) {
          // Create a this.<ref> for each field matching order of constructor arguments
          // List of Lists because we can have multiple parameter lists
          val conArgs: List[List[Tree]] =
            constructor.vparamss.map(_.map { vp =>
              val p = paramLookup(vp.name.toString)
              // Make this.<ref>
              val select = gen.mkAttributedSelect(thiz.asInstanceOf[Tree], p)
              // Clone any Data parameters to avoid field aliasing, need full clone to include direction
              if (isData(vp.symbol)) cloneTypeFull(select.asInstanceOf[Tree]) else select
            })

          val tparamList = bundle.tparams.map { t => Ident(t.symbol) }
          val ttpe =
            if (tparamList.nonEmpty) AppliedTypeTree(Ident(bundle.symbol), tparamList) else Ident(bundle.symbol)
          val newUntyped = New(ttpe, conArgs)
          val neww = localTyper.typed(newUntyped)

          // Create the symbol for the method and have it be associated with the Bundle class
          val cloneTypeSym =
            bundle.symbol.newMethod(TermName("_cloneTypeImpl"), bundle.symbol.pos.focus, Flag.OVERRIDE | Flag.PROTECTED)
          // Handwritten cloneTypes don't have the Method flag set, unclear if it matters
          cloneTypeSym.resetFlag(Flags.METHOD)
          // Need to set the type to chisel3.Bundle for the override to work
          cloneTypeSym.setInfo(NullaryMethodType(bundleTpe))

          additionalMethods ++= Seq(localTyper.typed(DefDef(cloneTypeSym, neww)))
        }

        // ==================== Generate val elements ====================

        /* Test to see if the bundle found is amenable to having it's elements
         * converted to an immediate form that will not require reflection
         */
        def isSupportedBundleType: Boolean = {
          arguments.buildElementsAccessor && !bundle.mods.hasFlag(Flag.ABSTRACT)
        }

//        def showInfo(info: Type): String = {
//          info.members.mkString("\n")
//        }

        if (isSupportedBundleType) {
          show(("#" * 80 + "\n") * 2)
          show(s"Processing: Bundle named: ${bundle.name.toString}")
          show(" ")
//          show(s"BundleType: ${bundle.symbol.typeSignature.toString}")
//          show("Bundle parents: \n" + bundle.impl.parents.map { parent =>
//            s"parent: ${parent.symbol.name} [${isBundle(parent.symbol)}] " +
//              s"IsBundle=" + isBundle(parent.symbol) + parent.symbol + "\n" +
////              "parent.symbol.info.decl: " + parent.symbol.info.decl(parent.symbol.info.decls.head.name). +
//              s"\nDecls::\n  " + showInfo(parent.symbol.info)
//          }.mkString("\n"))

          /* extract the true fields from the super classes a given bundle
           */
          def getAllBundleFields(bundleSymbol: Symbol, depth: Int = 0): List[(String, Tree)] = {

            def indentShow(s: => String): Unit = {
              val indentString = ("-" * depth) * 2 + ">  "
              s.split("\n").foreach { line =>
                show(indentString + line)
              }
            }

            def isBundleField(member: Symbol): Boolean = {
              if (member.isAccessor && isData(member.tpe.typeSymbol)) {
                indentShow(
                  s"\nProcessing member $member isMethod=${member.isMethod} isAccessor==${member.isAccessor}" +
                    s"\ntpe                ${member.tpe} " +
                    s"\nisData             ${isData(member.tpe.typeSymbol)} " +
                    ""
                )
                true
              } else if (typeIsOptionOfData(member.tpe)) {
                true
              } else {
                false
              }
            }

            indentShow(s"getAll: Current Bundle: ${bundleSymbol.name}")

            val currentFields = bundleSymbol.info.members.flatMap {

              case member if member.isPublic =>
                if (isBundleField(member)) {
                  indentShow(
                    s"  MATCHED: Bundle Member $member  isData=${isData(member)}" +
                      s" ${showRaw(member)} : ${showRaw(member.typeSignature)}"
                  )
                  // The params have spaces after them (Scalac implementation detail)
                  Some(member.name.toString.trim -> gen.mkAttributedSelect(thiz.asInstanceOf[Tree], member))
                } else {
                  //TODO: The following code block creates a compiler error for bundle fields that are
                  //      Seq[Data]. The test for this case is a bit too hacky so for now we will just
                  //      elide these fields.
//                  if (member.isAccessor && typeIsSeqOfData(member.tpe) && !isIgnoreSeqInBundle(bundleSymbol)) {
//                    global.reporter.error(
//                      member.pos,
//                      s"Bundle.field ${bundleSymbol.name}.${member.name} cannot be a Seq[Data]. " +
//                        "Use Vec or MixedVec or mix in trait IgnoreSeqInBundle"
//                    )
//                  }
                  None
                }

              case _ => None
            }.toList

            indentShow(s"\nstarting parents: ${bundleSymbol.parentSymbols.mkString(",")}")
            val allParentFields = bundleSymbol.parentSymbols.flatMap { parentSymbol =>
              val fieldsFromParent = if (depth < 1 && !isExactBundle(bundleSymbol)) {
                indentShow(s"Calling getAll($parentSymbol) ")
                val foundFields = getAllBundleFields(parentSymbol, depth + 1)
                indentShow(s"Return getAll($parentSymbol): " + foundFields.map(_._1).mkString(","))
                foundFields
              } else {
                List()
              }
              fieldsFromParent
            }
            allParentFields ++ currentFields
          }

          val elementArgs = getAllBundleFields(bundle.symbol)

          val elementsImplSym =
            bundle.symbol.newMethod(TermName("_elementsImpl"), bundle.symbol.pos.focus, Flag.OVERRIDE | Flag.PROTECTED)
          // Handwritten cloneTypes don't have the Method flag set, unclear if it matters
          elementsImplSym.resetFlag(Flags.METHOD)
          // Need to set the type to chisel3.Bundle for the override to work
          elementsImplSym.setInfo(NullaryMethodType(seqMapTpe))

          val elementsImpl = localTyper.typed(
            DefDef(elementsImplSym, q"scala.collection.immutable.SeqMap.apply[String, Any](..$elementArgs)")
          )

          //TODO: These should go away
          show("ELEMENTS:\n" + elementArgs.map { case (symbol, tree) => s"($symbol, $tree)" }.mkString("\n"))
//          show("ElementsImpl: " + showRaw(elementsImpl) + "\n\n\n")
//          show("ElementsImpl: " + elementsImpl + "\n\n\n")
          additionalMethods ++= Seq(elementsImpl)

          show(("#" * 80 + "\n") * 2)
        }

        // ==================== Generate _usingPlugin ====================
        // Unclear why quasiquotes work here but didn't for cloneTypeSym, maybe they could.
        val usingPlugin = localTyper.typed(q"override protected def _usingPlugin: Boolean = true")
        additionalMethods ++= Seq(usingPlugin)

        val withMethods = deriveClassDef(bundle) { t =>
          deriveTemplate(t)(_ ++ additionalMethods)
        }

        super.transform(localTyper.typed(withMethods))

      case _ => super.transform(tree)
    }
  }
}
