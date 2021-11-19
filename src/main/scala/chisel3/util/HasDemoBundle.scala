// SPDX-License-Identifier: Apache-2.0
//
//package chisel3
//
//import scala.language.reflectiveCalls
//
//import chisel3.experimental.{ChiselEnum, FixedPoint}
//import chisel3.stage.ChiselStage
//import chisel3.util.Decoupled
//
///* This file is here to provide a quicker path to modify and test the
// * BundleComponent plugin code as it take a long time to
// * compile all the test whenever the plugin changes
// */
//class BpipIsComplexBundle extends Module {
//
//  trait BpipVarmint {
//    val varmint = Bool()
//    def vermin = Bool()
//    private val puppy = Bool()
//  }
//
//  abstract class BpipAbstractBundle extends Bundle {
//    def doNothing: Unit
//
//    val fromAbstractBundle = UInt(22.W)
//  }
//
//  class BpipOneField extends Bundle {
//    val fieldOne = SInt(8.W)
//  }
//
//  class BpipTwoField extends BpipOneField {
//    val fieldTwo = SInt(8.W)
//    val fieldThree = Vec(4, UInt(12.W))
//  }
//  class BpipAnimalBundle(w1: Int, w2: Int) extends Bundle {
//    val dog = SInt(w1.W)
//    val fox = UInt(w2.W)
//  }
//
//  class BpipDemoBundle[T <: Data](gen: T, gen2: => T) extends BpipTwoField with BpipVarmint {
//    val foo = gen
//    val bar = Bool()
//    val qux = gen2
//    val bad = 44
//    val baz = Decoupled(UInt(16.W))
//    val animals = new BpipAnimalBundle(4, 8)
//  }
//
//  val out = IO(Output(new BpipDemoBundle(UInt(4.W), FixedPoint(10.W, 4.BP))))
//
//  val out2 = IO(Output(new BpipAbstractBundle {
//    override def doNothing: Unit = println("ugh")
//    val notAbstract:        Bool = Bool()
//  }))
//
//  val out4 = IO(Output(new BpipAnimalBundle(99, 100)))
//  val out5 = IO(Output(new BpipTwoField))
//
//  out := DontCare
//  out5 := DontCare
//
//  assert(!BundleComparator(out, showComparison = true), "Bundle BpipDemoBundle not the same")
//  assert(!BundleComparator(out5, showComparison = true), "Bundle BpipTwoField not the same")
//  assert(!BundleComparator(out2, showComparison = true), "Bundle BpipAbstractBundle not the same")
//  assert(!BundleComparator(out4, showComparison = true), "Bundle BpipAnimal not the same")
//}
//
///* Rich and complicated bundle example
// *
// */
//object DebugProblem1 {
//  def main(args: Array[String]): Unit = {
//    ChiselStage.emitFirrtl(new BpipIsComplexBundle)
//    println("done!")
//  }
//}
//
//trait BpipSuperTraitWithField {
//  val bpipSuperTraitGood = SInt(17.W)
//  def bpipSuperTraitBad = SInt(22.W)
//}
//
//trait BpipTraitWithField extends BpipSuperTraitWithField {
//  val bpipTraitGood = SInt(17.W)
//  def bpipTraitBad = SInt(22.W)
//}
//
//class BpipOneField extends Bundle with BpipTraitWithField {
////class BpipOneField extends Bundle {
//  val bpipOneFieldOne = SInt(8.W)
//  val bpipOneFieldTwo = SInt(8.W)
//}
//
//class BpipTwoField extends BpipOneField {
//  val bpipTwoFieldOne = SInt(8.W)
//  val bpipTwoFieldTwo = Vec(4, UInt(12.W))
//  val myInt = 7
//  val baz = Decoupled(UInt(16.W))
//}
//
//class BpipDecoupled extends BpipOneField {
//  val bpipDecoupledSInt = SInt(8.W)
//  val bpipDecoupledVec = Vec(4, UInt(12.W))
//  val bpipDecoupledDecoupled = Decoupled(UInt(16.W))
//}
//
//class DebugProblem2 extends Module {
//  val out1 = IO(Output(new BpipDecoupled))
//  assert(!BundleComparator(out1, showComparison = true), "BpipDecoupled failed to construct")
//}
//
///* plugin should work with decoupled
// *
// */
//object DebugProblem2 {
//  def main(args: Array[String]): Unit = {
//    ChiselStage.emitFirrtl(new DebugProblem2)
//  }
//}
//
///* plugin should not affect the seq detection
// *
// */
//class DebugProblem3 extends Module {
//  val out1 = IO(Output(new BpipTwoField))
//  assert(!BundleComparator(out1, showComparison = true))
//}
//
//object DebugProblem3 {
//  def main(args: Array[String]): Unit = {
//    ChiselStage.emitFirrtl(new DebugProblem3)
//    println("done!")
//  }
//}
//
//
////TODO: If you comment out this block and compile, there will be a compiler
////      compiler error at the badSeqField
//class BpipBadSeqBundle extends Bundle {
//  val bpipBadSeqBundleGood = UInt(999.W)
//  val bpipBadSeqBundleBad = Seq(UInt(16.W), UInt(8.W), UInt(4.W))
//}
//
///* plugin should not affect the seq detection
// *
// */
//class DebugProblem6 extends Module {
//  val out1 = IO(Output(new BpipBadSeqBundle))
//  println(s"out1.elements:\n" + out1.elements.map(e => s"${e._1} (${e._2})").mkString("\n"))
//}
//
//object DebugProblem6 {
//  def main(args: Array[String]): Unit = {
//    ChiselStage.emitFirrtl(new DebugProblem6)
//    println("done!")
//  }
//}
//
//class BpipBadSeqBundleWithIgnore extends Bundle with IgnoreSeqInBundle {
//  val goodFieldWithIgnore = UInt(999.W)
//  val badSeqFieldWithIgnore = Seq(UInt(16.W), UInt(8.W), UInt(4.W))
//}
//
///* plugin should not affect the seq detection
// *
// */
//class DebugProblem7 extends Module {
//  val out1 = IO(Output(new BpipBadSeqBundleWithIgnore))
//  assert(!BundleComparator(out1, showComparison = true), "BpipBadSeqBundleWithIgnore does not match old")
//}
//
//object DebugProblem7 {
//  def main(args: Array[String]): Unit = {
//    ChiselStage.emitFirrtl(new DebugProblem7)
//    println("done!")
//  }
//}
//
// This is mostly a test of the field order
//class BpipP8_1 extends Bundle {
//  val field_1_1 = UInt(11.W)
//  val field_1_2 = UInt(12.W)
//}
//
//class BpipP8_2 extends BpipP8_1 {
//  val field_2_1 = UInt(11.W)
//  val field_2_2 = UInt(12.W)
//}
//
//class BpipP8_3 extends BpipP8_2 {
//  val field_3_1 = UInt(11.W)
//  val field_3_2 = UInt(12.W)
//}
//
///* plugin should not affect the seq detection
// *
// */
//class DebugProblem8 extends Module {
//  val out1 = IO(Output(new BpipP8_3))
//  assert(!BundleComparator(out1, showComparison = true), "BpipP8_2 out of order")
//}
//
//object DebugProblem8 {
//  def main(args: Array[String]): Unit = {
//    ChiselStage.emitFirrtl(new DebugProblem8)
//    println("done!")
//  }
//}
//
///* plugin should allow parameter var fields
// */
//class DebugProblem9 extends Module {
//  // The following block does not work, suggesting that ParamIsField is not a case we need to solve
//  class BpipParamIsField0(val paramField0: UInt) extends Bundle
//  class BpipParamIsField1(val paramField1: UInt) extends BpipParamIsField0(UInt(66.W))
//
//  val out3 = IO(Output(new BpipParamIsField1(UInt(10.W))))
//  val out4 = IO(Output(new BpipParamIsField1(UInt(10.W))))
//  // println(s"ParamsIsField.elements:\n" + out3.elements.map(e => s"${e._1} (${e._2})").mkString("\n"))
//  out3 := DontCare
//  BundleComparator(out3, showComparison = true)
//  BundleComparator(out4, showComparison = true)
//}
//
//object DebugProblem9 {
//  def main(args: Array[String]): Unit = {
//    ChiselStage.emitFirrtl(new DebugProblem9)
//    println("done!")
//  }
//}
//
//class DebugProblem10Module extends Module {
//
//  class OtherBundle extends Bundle {
//    val otherField = UInt(55.W)
//  }
//
//  class BpipWithGen[T <: Data, TT <: Data](gen: T, gen2: => TT) extends Bundle {
//    val superFoo = gen
//    val superQux = gen2
//  }
//
//  class BpipUsesWithGen[T <: Data](gen: T, gen2: => T) extends BpipWithGen(gen, gen2) {
//    //    val foo = gen
//    val bar = Bool()
//    val qux = gen2
//    val bad = 444
//    val baz = Decoupled(UInt(16.W))
//  }
//
//  val out1 = IO(Output(new BpipUsesWithGen(UInt(4.W), new OtherBundle)))
//  val out2 = IO(Output(new BpipUsesWithGen(UInt(4.W), FixedPoint(10.W, 4.BP))))
//
//
//  assert(!BundleComparator(out1, showComparison = true), "Bundle BpipUsesWithGen not the same")
//  assert(!BundleComparator(out2, showComparison = true), "Bundle BpipUsesWithGen not the same")
//}
//
///* Testing whether gen fields superFoo and superQux can be found when they are
// * declared in a superclass
// *
// */
//object DebugProblem10 {
//  def main(args: Array[String]): Unit = {
//    ChiselStage.emitFirrtl(new DebugProblem10Module)
//    println("done!")
//  }
//}
//
//class DebugProblem11Module extends Module {
//  class BpipWithGen[T <: Data](gen: T) extends Bundle {
//    val superFoo = gen
//    val superQux = gen
//  }
//
////  class BpipDemoBundle[T <: Data](gen: T, gen2: => T) extends BpipTwoField with BpipVarmint {
//  class BpipUsesWithGen[T <: Data](gen: T) extends BpipWithGen(gen) {
////    val firstGenField = gen
////    val secondGenField = gen
//  }
//
//  val out = IO(Output(new BpipUsesWithGen(UInt(4.W))))
//
//  out := DontCareI'll th
//
//  assert(!BundleComparator(out, showComparison = true), "Bundle BpipDemoBundle not the same")
//
//  println(s"Testing call ${out.elements.map(_._1).mkString(",")}")
//}
//
///* Testing whether gen fields superFoo and superQux can be found when they are
// * declared in a superclass
// *
// */
//object DebugProblem11 {
//  def main(args: Array[String]): Unit = {
//    ChiselStage.emitFirrtl(new DebugProblem11Module)
//    println("done!")
//  }
//}
//
//class BpipBadBundleWithHardware extends Bundle {
//  val bpipWithHardwareGood = UInt(8.W)
//  val bpipWithHardwareBad = 244.U(16.W)
//}
//
//class BpipExtendsBadBundleWithHardware extends BpipBadBundleWithHardware {
//  val bpipExtendsWithHardwareSInt = SInt(8.W)
//}
//
//class DebugProblem12 extends Module {
//  val out = IO(Output(new BpipBadBundleWithHardware))
//  assert(!BundleComparator(out, showComparison = true), "BpipExtendsBadBundleWithHardware failed to construct")
//}
//
///* plugin should error correctly when bundles contain hardware
// *
// */
//object DebugProblem12 {
//  def main(args: Array[String]): Unit = {
//    ChiselStage.emitFirrtl(new DebugProblem12)
//  }
//}
//
// In contrast to Problem 11, this is legal because of =>
//class DebugProblem13Module extends Module {
//  class BpipWithGen[T <: Data](gen: => T) extends Bundle {
//    val superFoo = gen
//    val superQux = gen
//  }
//
//  //  class BpipDemoBundle[T <: Data](gen: T, gen2: => T) extends BpipTwoField with BpipVarmint {
//  class BpipUsesWithGen[T <: Data](gen: =>T) extends BpipWithGen(gen) {
//    //    val firstGenField = gen
//    //    val secondGenField = gen
//  }
//
//  val out = IO(Output(new BpipUsesWithGen(UInt(4.W))))
//
//  out := DontCare
//
//  assert(!BundleComparator(out, showComparison = true), "Bundle BpipDemoBundle not the same")
//
//  println(s"Testing call ${out.elements.map(_._1).mkString(",")}")
//}
//
///* Testing whether gen fields superFoo and superQux can be found when they are
// * declared in a superclass
// *
// */
//object DebugProblem13 {
//  def main(args: Array[String]): Unit = {
//    ChiselStage.emitFirrtl(new DebugProblem13Module)
//    println("done!")
//  }
//}
//
//class OptionBundle(val hasIn: Boolean) extends Bundle {
//  val in = if (hasIn) {
//    Some(Input(Bool()))
//  } else {
//    None
//  }
//  val out = Output(Bool())
//}
//
//class DebugProblem14 extends Module {
//  val outTrue = IO(Output(new OptionBundle(hasIn = true)))
//  val outFalse = IO(Output(new OptionBundle(hasIn = false)))
//  assert(!BundleComparator(outTrue, showComparison = true), "DebugProblem14 failed to construct")
//  assert(!BundleComparator(outFalse, showComparison = true), "DebugProblem14 failed to construct")
//}
//
///* plugin should error correctly when bundles contain hardware
// *
// */
//object DebugProblem14 {
//  def main(args: Array[String]): Unit = {
//    ChiselStage.emitFirrtl(new DebugProblem14)
//  }
//}
//
//object Enum0 extends ChiselEnum {
//  val s0, s1, s2 = Value
//}
//
//class Bundle0 extends Bundle {
//  val a = UInt(8.W)
//  val b = Bool()
//  val c = Enum0.Type
//}
//
//class DebugProblem15 extends Module {
//  val out = IO(Output(new Bundle0))
//  assert(!BundleComparator(out, showComparison = true), "DebugProblem15 failed to construct")
//}
//
///* plugin should error correctly when bundles contain hardware
// *
// */
//object DebugProblem15 {
//  def main(args: Array[String]): Unit = {
//    ChiselStage.emitFirrtl(new DebugProblem15)
//  }
//}
//
///* plugin should error correctly when bundles contain only a Option field
// *
// */
//object DebugProblem16 {
//  def main(args: Array[String]): Unit = {
//    ChiselStage.emitFirrtl(new Module {
//      val io = IO(new Bundle {
//        val foo = Input(UInt(8.W))
//        val x = new Bundle {
//          val y = if (false) Some(Input(UInt(8.W))) else None
//        }
//      })
//      BundleComparator(io, showComparison = true)
//      BundleComparator(io.x, showComparison = true)
//    })
//  }
//}
//
