// SPDX-License-Identifier: Apache-2.0

package chisel3

import chisel3.experimental.conversions.seq2vec

import scala.language.reflectiveCalls
import chisel3.experimental.{ChiselEnum, FixedPoint}
import chisel3.stage.ChiselStage
import chisel3.util._

import scala.math.min

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
///* plugin should error correctly when bundles contain only a Option field
// *
// */
//
//object DebugProblem17 {
//  implicit class BooleanToAugmentedBoolean(private val x: Boolean) extends AnyVal {
//    def toInt: Int = if (x) 1 else 0
//
//    // this one's snagged from scalaz
//    def option[T](z: => T): Option[T] = if (x) Some(z) else None
//  }
//
//  case class ALUConfig(
//    xLen: Int,
//    mul:  Boolean,
//    b:    Boolean)
//
//  class BitManIO extends Bundle {
//    val funct3 = Input(UInt(3.W))
//    val funct7 = Input(UInt(7.W))
//  }
//
//  class ALU(c: ALUConfig) extends Module {
//
//    class BpipOptionBundle extends Bundle with IgnoreSeqInBundle {
//      val bpipUIntVal = Input(UInt(8.W))
//      lazy val bpipUIntLazyVal = Input(UInt(8.W))
//      var bpipUIntVar = Input(UInt(8.W))
//      def bpipUIntDef = Input(UInt(8.W))
//
////      val bpipOptionUInt = Some(Input(UInt(16.W)))
////      val bpipOptionOfBundle = c.b.option(new BitManIO)
//      val bpipSeqData = Seq(UInt(8.W), UInt(8.W))
//    }
//
//    val io = IO(new BpipOptionBundle)
//    BundleComparator(io, showComparison = true)
//  }
//
//  def main(args: Array[String]): Unit = {
//    ChiselStage.emitFirrtl(new ALU(ALUConfig(10, mul = true, b = false)))
//  }
//}
///* special case found in testing
// *
// */
//
//object DebugProblem18 {
//  class Bundle0 extends Bundle {
//    val a = UInt(8.W)
//    val b = Bool()
//    val c = Enum0.Type
//  }
//
//  class Bundle1 extends Bundle {
//    val a = new Bundle0
//    val b = Vec(4, Vec(4, Bool()))
//  }
//
//  class Module0 extends Module {
//    val i = IO(Input(new Bundle1))
//    val o = IO(Output(new Bundle1))
//    val r = Reg(new Bundle1)
//    o := r
//    r := i
//
//    BundleComparator(i, showComparison = true)
//    BundleComparator(o, showComparison = true)
//    BundleComparator(r, showComparison = true)
////    traceName(r)
////    traceName(i)
////    traceName(o)
//  }
//
//  class Module1 extends Module {
//    val i = IO(Input(new Bundle1))
//    val m0 = Module(new Module0)
//    m0.i := i
//    m0.o := DontCare
//    BundleComparator(i, showComparison = true)
//
//  }
//
//  object Enum0 extends ChiselEnum {
//    val s0, s1, s2 = Value
//  }
//
//
//
//  def main(args: Array[String]): Unit = {
//    ChiselStage.emitFirrtl(new Module1)
//  }
//}

object ALUTester {
  object Split {

    import ALU._

    def apply(x: UInt, n0: Int) = {
      val w = x.getWidth
      (x.extract(w - 1, n0), x.extract(n0 - 1, 0))
    }

    def apply(x: UInt, n1: Int, n0: Int) = {
      val w = x.getWidth
      (x.extract(w - 1, n1), x.extract(n1 - 1, n0), x.extract(n0 - 1, 0))
    }

    def apply(x: UInt, n2: Int, n1: Int, n0: Int) = {
      val w = x.getWidth
      (x.extract(w - 1, n2), x.extract(n2 - 1, n1), x.extract(n1 - 1, n0), x.extract(n0 - 1, 0))
    }
  }


  object ALU {

    // Fill 1s from low bits to high bits
    def leftOR(x: UInt): UInt = leftOR(x, x.getWidth, x.getWidth)

    def leftOR(x: UInt, width: Integer, cap: Integer = 999999): UInt = {
      val stop = min(width, cap)

      def helper(s: Int, x: UInt): UInt =
        if (s >= stop) x else helper(s + s, x | (x << s) (width - 1, 0))

      helper(1, x)(width - 1, 0)
    }

    // Fill 1s from high bits to low bits
    def rightOR(x: UInt): UInt = rightOR(x, x.getWidth, x.getWidth)

    def rightOR(x: UInt, width: Integer, cap: Integer = 999999): UInt = {
      val stop = min(width, cap)

      def helper(s: Int, x: UInt): UInt =
        if (s >= stop) x else helper(s + s, x | (x >> s))

      helper(1, x)(width - 1, 0)
    }


    implicit class BooleanToAugmentedBoolean(private val x: Boolean) extends AnyVal {
      def toInt: Int = if (x) 1 else 0

      // this one's snagged from scalaz
      def option[T](z: => T): Option[T] = if (x) Some(z) else None
    }

    implicit class IntToAugmentedInt(private val x: Int) extends AnyVal {
      // exact log2
      def log2: Int = {
        require(isPow2(x))
        log2Ceil(x)
      }
    }

    implicit class UIntToAugmentedUInt(private val x: UInt) extends AnyVal {
      def sextTo(n: Int): UInt = {
        require(x.getWidth <= n, s"input width ${x.getWidth} must be <= padded width ${n}")
        if (x.getWidth == n) x
        else Cat(Fill(n - x.getWidth, x(x.getWidth - 1)), x)
      }

      def padTo(n: Int): UInt = {
        require(x.getWidth <= n, s"input width ${x.getWidth} must be <= padded width ${n}")
        if (x.getWidth == n) x
        else Cat(0.U((n - x.getWidth).W), x)
      }

      /** shifts left by n if n >= 0, or right by -n if n < 0 */
      def <<(n: SInt): UInt = {
        val w = n.getWidth - 1
        require(w <= 30, s"left shift amount ${w} is too big")

        val shifted = x << n(w - 1, 0)
        Mux(n(w), shifted >> (1 << w), shifted)
      }

      /** shifts right by n if n >= 0, or left by -n if n < 0 */
      def >>(n: SInt): UInt = {
        val w = n.getWidth - 1
        require(w <= 30, s"left shift amount ${w} is too big")

        val shifted = x << (1 << w) >> n(w - 1, 0)
        Mux(n(w), shifted, shifted >> (1 << w)).asUInt
      }

      /** Like UInt.apply(hi, lo), but returns 0.U for zero-width extracts */
      def extract(hi: Int, lo: Int): UInt = {
        require(hi >= lo - 1, s"extract hi ${hi} should be above lo ${lo}")
        if (hi == lo - 1) 0.U
        else x(hi, lo)
      }

      /** Like Some(UInt.apply(hi, lo)), but returns None for zero-width extracts */
      def extractOption(hi: Int, lo: Int): Option[UInt] = {
        require(hi >= lo - 1, s"extract hi ${hi} should be above lo ${lo}")
        if (hi == lo - 1) None
        else Some(x(hi, lo))
      }

      /** Extract with variable bounds */
      def extract(hi: UInt, lo: UInt): UInt = {
        (x.passBitsRight(hi) >> lo).asUInt
      }

      /** Zero out the bits above (hi + offset) (pass [hi+offset:0]) */
      def passBitsRight(hi: UInt, offset: Int = 0): UInt = {
        val absOffset = if (offset >= 0) offset else -offset
        // make sure mask is large enough to cover the width of the UInt we're masking and the largest bit position value we could pass in
        require(hi.getWidth <= 30, s"hi.getWidth=${hi.getWidth} is too big")
        val maskWidth = x.getWidth.max(1 << hi.getWidth)
        val hiOH =
          if (offset >= 0) {
            UIntToOH(hi, maskWidth) << absOffset
          }
          else {
            UIntToOH(hi, maskWidth + absOffset) >> absOffset
          }
        (x & rightOR(hiOH)) (x.getWidth - 1, 0)
      }

      /** Zero out the bits below (lo + offset) (pass [msb:lo+offset]) */
      def passBitsLeft(lo: UInt, offset: Int = 0): UInt = {
        val absOffset = if (offset >= 0) offset else -offset
        // make sure mask is large enough to cover the width of the UInt we're masking and the largest bit position value we could pass in
        require(lo.getWidth <= 30, s"lo.getWidth=${lo.getWidth} is too big")
        val maskWidth = x.getWidth.max(1 << lo.getWidth)
        val loOH =
          if (offset >= 0) {
            UIntToOH(lo, maskWidth) << absOffset
          }
          else {
            UIntToOH(lo, maskWidth + absOffset) >> absOffset
          }
        (x & leftOR(loOH)) (x.getWidth - 1, 0)
      }

      /** like x & ~y, but first truncate or zero-extend y to x's width */
      def andNot(y: UInt): UInt = x & ~(y | (x & 0.U))

      def rotateRight(n: Int): UInt = {
        if (x.getWidth <= 1 || n == 0) x
        else if (n >= x.getWidth) rotateRight(n % x.getWidth)
        else Cat(x(n - 1, 0), x >> n)
      }

      def rotateRight(n: UInt): UInt = {
        if (x.getWidth <= 1) {
          x
        } else {
          val amt = n.padTo(log2Ceil(x.getWidth))
          (0 until log2Ceil(x.getWidth)).foldLeft(x)((r, i) => Mux(amt(i), r.rotateRight(1 << i), r))
        }
      }

      def rotateLeft(n: Int): UInt = {
        if (x.getWidth <= 1 || n == 0) x
        else if (n >= x.getWidth) rotateLeft(n % x.getWidth)
        else Cat(x(x.getWidth - 1 - n, 0), x(x.getWidth - 1, x.getWidth - n))
      }

      def rotateLeft(n: UInt): UInt = {
        if (x.getWidth <= 1) {
          x
        } else {
          val amt = n.padTo(log2Ceil(x.getWidth))
          (0 until log2Ceil(x.getWidth)).foldLeft(x)((r, i) => Mux(amt(i), r.rotateLeft(1 << i), r))
        }
      }

      /** compute (this + y) % n, given (this < n) and (y < n) */
      def addWrap(y: UInt, n: Int): UInt = {
        val z = x +& y
        if (isPow2(n)) z(n.log2 - 1, 0) else Mux(z >= n.U, z - n.U, z)(log2Ceil(n) - 1, 0)
      }

      /** compute (this - y) % n, given (this < n) and (y < n) */
      def subWrap(y: UInt, n: Int): UInt = {
        val z = x -& y
        if (isPow2(n)) z(n.log2 - 1, 0) else Mux(z(z.getWidth - 1), z + n.U, z)(log2Ceil(n) - 1, 0)
      }

      /** Count trailing zeros; result is unspecified if input is zero */
      def ctz: UInt = x.getWidth match {
        case 0 | 1 => 0.U
        case 2 => !x(0)
        case w =>
          val mid = 1 << (log2Ceil(w) - 1)
          val (hi, lo) = Split(x, mid)
          Mux(lo.orR, lo.ctz, mid.U | hi.ctz)
      }

      def grouped(width: Int): Seq[UInt] =
        (0 until x.getWidth by width).map(base => x(base + width - 1, base))

      def inRange(base: UInt, bounds: UInt) = x >= base && x < bounds

      def ##(y: Option[UInt]): UInt = y.map(x ## _).getOrElse(x)

      /** Like >=, but prevents x-prop for ('X >= 0) case */
      def >==(y: UInt): Bool = x >= y || y === 0.U
    }

    object FN {
      val SZ = 5
      val X = BitPat.dontCare(SZ)

      val ADD = 0.U
      val XOR = 1.U
      val OR = 2.U
      val AND = 3.U
      val SUB = 4.U
      val SLT = 6.U
      val SLTU = 7.U
      val SL = 8.U
      val SR = 10.U
      val SRA = 11.U
      val MUL = 12.U
      val MULH = 13.U
      val MULHSU = 14.U
      val MULHU = 15.U

      val XNOR = 16.U
      val ORN = 17.U
      val ANDN = 18.U
      val SHADD = 19.U
      val CNT = 20.U
      val MINMAX = 21.U
      val SEXT = 22.U
      val ZEXT = 23.U
      val GREV = 24.U
      val GORC = 25.U
      val SHADDW = 26.U
      val ADDW = 27.U
      val SLLIW = 28.U
      val CNTW = 29.U
    }

    def isAdder(cmd: UInt): Bool = cmd === FN.ADD || cmd === FN.SUB

    def isSub(cmd: UInt): Bool = cmd(4, 2) === 1.U

    def isCmp(cmd: UInt): Bool = cmd(4, 1) === 3.U

    def isShift(cmd: UInt): Bool = cmd(4, 2) === 2.U

    def shiftRight(cmd: UInt): Bool = cmd(1)

    def shiftArith(cmd: UInt): Bool = cmd(0)

    def isMul(cmd: UInt): Bool = cmd(4, 2) === 3.U
  }

  case class ALUConfig(
                        xLen: Int,
                        mul: Boolean,
                        b: Boolean,
                      )

  class BitManIO extends Bundle {
    val funct3 = Input(UInt(3.W))
    val funct7 = Input(UInt(7.W))
  }

  class ALU(c: ALUConfig) extends Module {

    import ALU._

    val io = IO(new Bundle {
      val dw = Input(Bool())
      val fn = Input(UInt(FN.SZ.W))
      val fct = c.b.option(new BitManIO)
      val in2 = Input(UInt(c.xLen.W))
      val in1 = Input(UInt(c.xLen.W))
      val out = Output(UInt(c.xLen.W))
      val adder_out = Output(UInt(c.xLen.W))
    })

    def extend(x: UInt, dw: Bool, signed: Bool): UInt = c.xLen match {
      case 32 => x
      case 64 => Cat(Mux(dw, x(63, 32), Fill(32, signed && x(31))), x(31, 0))
      //    case 10 => x
      case _ =>
        throw new Exception("how the hell did i get here")
    }

    def formShiftAmount(x: UInt, dw: Bool): UInt = c.xLen match {
      case 32 => x(4, 0)
      case 64 => Cat(x(5) && dw, x(4, 0))
      //    case 10 => x
      case _ =>
        throw new Exception("how the hell did i get here")
    }

    def shiftresult(x: UInt, dw: Bool): UInt = c.xLen match {
      case 32 => x(2 * c.xLen - 1, c.xLen)
      case 64 => Cat(x(5) && dw, x(4, 0))
      case _ =>
        throw new Exception("how the hell did i get here")
    }

    // B-extension
    def x64w = (c.xLen == 64).asBool && !io.dw

    def b = c.b.asBool

    def b64 = b && (c.xLen == 64).asBool

    def f3 = io.fct.map(_.funct3).getOrElse(0.U)

    def f7 = io.fct.map(_.funct7).getOrElse(0.U)

    def addw = b64 && (io.fn === FN.SHADDW || io.fn === FN.ADDW)

    def shiftw = b64 && io.fn === FN.SLLIW

    def cntw = b64 && io.fn === FN.CNTW

    def shadd = b && io.fn === FN.SHADD

    def shaddw = b64 && io.fn === FN.SHADDW

    def logicn = b && (io.fn === FN.XNOR || io.fn === FN.ORN || io.fn === FN.ANDN)

    def rotate = b && isShift(io.fn) && f7(5, 4) === 3.U

    def minmax = b && io.fn === FN.MINMAX

    // ADD, SUB
    val in1_mask = Mux(addw || shiftw || cntw, io.in1(31, 0), io.in1)
    println(s"f3(2, 1) is '${f3(2, 1)}''")

    val in1_shf = (in1_mask << Mux(shadd || shaddw, f3(2, 1), 0.U)) (c.xLen - 1, 0)
    val sub = isSub(io.fn) || minmax
    val in2_inv = Mux(sub || logicn || rotate, ~io.in2, io.in2)
    io.adder_out := in1_shf + in2_inv + sub

    // SLT, SLTU
    val slt = {
      val cmpUnsigned = io.fn === FN.SLTU || (minmax && f3(0))

      Mux(io.in1(c.xLen - 1) === io.in2(c.xLen - 1), io.adder_out(c.xLen - 1), Mux(cmpUnsigned, io.in2(c.xLen - 1), io.in1(c.xLen - 1)))
    }

    // SLL, SRL, SRA, optionally MUL
    val shout = if (!c.mul && !c.b) {
      val shamt = formShiftAmount(io.in2, io.dw)
      val shin_r = extend(io.in1, io.dw, shiftArith(io.fn))
      val shin = Mux(shiftRight(io.fn), shin_r, Reverse(shin_r))
      val shout_r = (Cat(shiftArith(io.fn) & shin(c.xLen - 1), shin).asSInt >> shamt) (c.xLen - 1, 0)
      val shout_l = Reverse(shout_r)

      Mux(isShift(io.fn) && shiftRight(io.fn), shout_r, 0.U) |
        Mux(isShift(io.fn) && !shiftRight(io.fn), shout_l, 0.U)
    } else if (!c.mul && c.b) {
      val shamt = formShiftAmount(io.in2, io.dw)
      val rotate_amt = Mux(shiftRight(io.fn), shamt, -shamt & (c.xLen - 1).U)
      val shin = extend(in1_mask, io.dw, shiftArith(io.fn))
      val shift_out = Cat(shiftArith(io.fn) & shin(c.xLen - 1), shin << (c.xLen - 1)).asSInt >> rotate_amt
      val shift_out_right = shift_out(2 * c.xLen - 2, c.xLen - 1)
      val shift_out_left = shift_out(c.xLen - 2, 0) << 1
      val rotate_out_left_word = shift_out(c.xLen - 2, c.xLen / 2 - 1)
      val is_shift_zero = shamt === 0.U
      val is_shfit = isShift(io.fn) || shiftw
      val is_shift_right = is_shfit && (shiftRight(io.fn) || (!shiftRight(io.fn) && is_shift_zero) || rotate)
      val is_shift_left = is_shfit && (!shiftRight(io.fn) || rotate)

      Mux(is_shift_right, shift_out_right, 0.U) |
        Mux(is_shift_left, shift_out_left, 0.U) |
        Mux(x64w && rotate, rotate_out_left_word, 0.U)
    } else {
      val lhs_signed = Mux(isMul(io.fn), (io.fn(1, 0) =/= 3.U), shiftArith(io.fn))
      val lhs_but_sign = extend(in1_mask, io.dw, shiftArith(io.fn))
      val lhs = Cat(lhs_signed && lhs_but_sign(c.xLen - 1), lhs_but_sign).asSInt
      val rhs_signed = Mux(isMul(io.fn), !io.fn(1), false.B)
      val shamt_l = formShiftAmount(io.in2, io.dw)
      val (shamt_zero, shamt_r) = Split(0.U -& shamt_l, log2Ceil(c.xLen))
      val shamt = Mux(shiftRight(io.fn), shamt_r, shamt_l)
      val rhs = Cat(rhs_signed && io.in2(c.xLen - 1), Mux(isMul(io.fn), io.in2, 1.U << shamt)).asSInt
      val product = lhs * rhs
      val shift_out_right = product(2 * c.xLen - 1, c.xLen)
      val shift_out_left = product(c.xLen - 1, 0)
      val rotate_out_left_word = product(c.xLen - 1, c.xLen / 2)
      val is_shfit = isShift(io.fn) || shiftw
      val is_shift_right = is_shfit && ((shiftRight(io.fn) && shamt_zero(0).asBool) || rotate)
      val is_shift_left = is_shfit && (!(shiftRight(io.fn) && shamt_zero(0).asBool) || rotate)
      val want_hi = Mux(isMul(io.fn), io.fn(1, 0) =/= 0.U, is_shift_right)
      val want_lo = Mux(isMul(io.fn), io.fn(1, 0) === 0.U, is_shift_left)

      Mux(want_hi, shift_out_right, 0.U) |
        Mux(want_lo, shift_out_left, 0.U) |
        Mux(x64w && rotate, rotate_out_left_word, 0.U)
    }

    // AND, OR, XOR
    val logic = {
      val or = io.fn === FN.OR || (b && io.fn === FN.ORN)
      val xor = io.fn === FN.XOR || (b && io.fn === FN.XNOR)
      val and = io.fn === FN.AND || (b && io.fn === FN.ANDN)
      val in1_xor_in2 = io.in1 ^ in2_inv
      val in1_and_in2 = io.in1 & in2_inv
      Mux(xor || or, in1_xor_in2, 0.U) |
        Mux(or || and, in1_and_in2, 0.U)
    }

    // B-extension
    val bout = if (c.b) {
      val minmax = Mux(slt =/= f3(1), io.in1, 0.U) | Mux(slt === f3(1), io.in2, 0.U)
      val cnt = {
        val pcnt = PopCount(in1_mask)
        val rev = Reverse(io.in1) | (BigInt(1) << c.xLen).U
        val clz = Mux(x64w, rev >> c.xLen / 2, rev)
        val ctz = Mux(x64w, (BigInt(1) << c.xLen / 2).U, (BigInt(1) << c.xLen).U) | io.in1
        val zcnt = PriorityEncoder(Mux(io.in2(1, 0) === 0.U, clz, ctz))
        Mux(io.in2(1, 0) === 2.U, pcnt, zcnt)
      }
      val ext = {
        val is_zexth = io.fn === FN.ZEXT
        val is_sextbh = io.fn === FN.SEXT
        val is_sextb = is_sextbh && !io.in2(0)
        val is_sexth = is_sextbh && io.in2(0)
        val b15_0 = Cat(Fill(8, is_sextb && io.in1(7)) | Mux(is_sexth || is_zexth, io.in1(15, 8), 0.U), Mux(is_sextbh || is_zexth, io.in1(7, 0), 0.U))
        val sign = b15_0(15) && is_sextbh
        Cat(Fill(c.xLen - 16, sign), b15_0)
      }
      val rev8 = (0 until c.xLen / 8).map(i => io.in1(i * 8 + 7, i * 8)).reverse.asUInt
      val orcb = (0 until c.xLen / 8).map(i => Fill(8, io.in1(i * 8 + 7, i * 8) =/= 0.U)).asUInt

      Mux(io.fn === FN.CNT || io.fn === FN.CNTW, cnt, 0.U) |
        Mux(io.fn === FN.MINMAX, minmax, 0.U) |
        Mux(io.fn === FN.SEXT || io.fn === FN.ZEXT, ext, 0.U) |
        Mux(io.fn === FN.GREV, rev8, 0.U) |
        Mux(io.fn === FN.GORC, orcb, 0.U)
    } else 0.U

    // Last Mux
    val shift_logic = (isCmp(io.fn) && slt) | logic | shout | bout
    val out = Mux(isAdder(io.fn) || shadd || addw, io.adder_out, 0.U) | shift_logic

    io.out := extend(out, io.dw, true.B)
  }

  def main(args: Array[String]): Unit = {
    val firrtl = (new ChiselStage).emitFirrtl(new ALU(ALUConfig(32, mul = false, b = true)), args = Array("--full-stacktrace"))
    println(s"firrlt:\n$firrtl")
    //      ChiselStage.emitFirrtl(new ALU(ALUConfig(10, mul = true, b = false)))
  }
}