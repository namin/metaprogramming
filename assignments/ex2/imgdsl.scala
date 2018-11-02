package imgdsl

import lms.verify._

// Ported by Oleg Kiselyov's "A DSL for image manipulation"
// http://okmij.org/ftp/meta-programming/tutorial/

// With LMS-verify,
// we leave out the image reading / and writing to the "main" method,
// and generate a processing unit that take the in-place image.

trait ImgDsl {
  type E
  def int(i: Int): E
  def it: E
  def infix_+%(a: E, b: E): E
  def infix_-%(a: E, b: E): E
  def infix_*%(a: E, b: E): E
  def infix_<%(a: E, b: E): E
  def infix_>%(a: E, b: E): E
  def infix_=%(a: E, b: E): E
  def if_(cond: E, thenp: E, elsep: E): E
  // iteration loop is implicit

  def suffix: String = ""
}

// A library for reading and writing grayscale images,
// used in interpreter mode. In compilation mode,
// we use PGMA_IO.
object grayimg {
  type Pixel = Int

  case class Img(width: Int, height: Int, pixels: Array[Pixel])

  def rgb2gray(rgb: Int): Pixel = {
    val r = (rgb >> 16) & 0xFF;
    val g = (rgb >> 8) & 0xFF;
    val b = (rgb & 0xFF);
    val grayLevel = (r + g + b) / 3
    grayLevel
  }
  def gray2rgb(grayLevel: Pixel): Int = {
    val gray = (grayLevel << 16) + (grayLevel << 8) + grayLevel
    gray
  }

  import java.awt.image.BufferedImage
  import javax.imageio.ImageIO
  import java.io.File

  def read_img(fn: String): Img = {
    val o = ImageIO.read(new File(fn+".jpg"))
    val w = o.getWidth
    val h = o.getHeight
    val a = new Array[Pixel](w*h)
    for (i <- 0 until w)
      for (j <- 0 until h)
        a(i*h+j) = rgb2gray(o.getRGB(i, j))
    Img(w, h, a)
  }

  def write_img(fullfn: String, m: Img): Unit = {
    val w = m.width
    val h = m.height
    val o = new BufferedImage(w, h, BufferedImage.TYPE_INT_RGB)
    for (i <- 0 until w)
      for (j <- 0 until h)
        o.setRGB(i, j, gray2rgb(m.pixels(i*h+j)))

    ImageIO.write(o, "jpg", new File(fullfn))
  }

  def display_img(m: Img, suffix: String, cmd: String = "open"): Unit = {
    val outfile = s"out$suffix.jpg"
    write_img(outfile, m)
    import sys.process._
    import scala.language.postfixOps
    s"open $outfile" !
  }
}

trait ImgInterp extends ImgDsl {
  import grayimg._

  abstract class Value
  case class I(v: Int) extends Value
  case class B(v: Boolean) extends Value

  override type E = Value => Value
  override def int(i: Int): E = ???
  override def it: E = ???
  override def infix_+%(a: E, b: E): E = ???
  override def infix_-%(a: E, b: E): E = ???
  override def infix_*%(a: E, b: E): E = ???
  override def infix_<%(a: E, b: E): E = ???
  override def infix_>%(a: E, b: E): E = ???
  override def infix_=%(a: E, b: E): E = ???
  override def if_(cond: E, thenp: E, elsep: E): E = ???

  def iterate(img: Img)(f: E): Unit = img match {
    case Img(w,h,ps) =>
      for (i <- 0 until w) {
        for (j <- 0 until h) {
          val x = i*h+j
          ps(x) = f(I(ps(x))) match {
            case I(v) => v
          }
        }
      }
  }
  def run(f: E): Unit = {
    val img = read_img("takaosan")
    iterate(img)(f)
    display_img(img, suffix)
  }
}


trait ImgComp extends ImgDsl with Dsl {
  abstract class SValue
  case class I(c: Rep[Int]) extends SValue
  case class B(c: Rep[Boolean]) extends SValue

  override type E = SValue => SValue
  override def int(i: Int): E = ???
  override def it: E = ???
  override def infix_+%(a: E, b: E): E = ???
  override def infix_-%(a: E, b: E): E = ???
  override def infix_*%(a: E, b: E): E = ???
  override def infix_<%(a: E, b: E): E = ???
  override def infix_>%(a: E, b: E): E = ???
  override def infix_=%(a: E, b: E): E = ???
  override def if_(cond: E, thenp: E, elsep: E): E = ???

  def iterate(w: Rep[Int], h: Rep[Int], ps: Rep[Array[Int]])(f: E): Rep[Unit] =
    for (i <- 0 until w) {
      loop_assigns(list_new(i::(ps within (0 until w*h))::Nil))
      val r = i*h
      for (j <- 0 until h) {
        loop_invariant(r == i*h)
        //??? more loop invariants
        loop_assigns(list_new(j::(ps within (0 until w*h))::Nil))
        val x = r+j
        ps(x) = f(I(ps(x))) match {
          case I(v) => v
        }
      }
    }

  def N: Int = 100 // ghost maximum dimension to avoid overflows
  def run(f: E) = {
    toplevel("p", { (w: Rep[Int], h: Rep[Int], ps: Rep[Array[Int]]) =>
      requires(0 < w && w < N)
      requires(0 < h && h < N)
      requires(valid(ps, 0 until w*h))
      reflectMutableInput(ps)
      iterate(w, h, ps)(f)
    })
  }
}

object imgdsl_examples {

trait Ex extends ImgDsl {
  def i: Int
  def res: E
  def test(): Unit

  override def suffix: String = i.toString
}

trait Ex1 extends Ex {
  override def i = 1
  override def res =
    int(1) +% int(2) *% int(3)
}

trait Ex2 extends Ex {
  override def i = 2
  override def res =
    if_(int(1) >% int(3), int(4), int(5))
}

trait Ex3 extends Ex {
  override def i = 3
  override def res =
    it
}

trait Ex4 extends Ex {
  override def i = 4
  override def res =
    if_(it >% int(120), it, int(0))
}

trait Ex5 extends Ex {
  override def i = 5
  override def res =
    if_(it >% int(128), int(2) *% (it -% int(128)), int(0))
}

trait Ex6 extends Ex {
  override def i = 6
  override def res =
    if_(it >% int(200), int(250), int(0))

}
}

import imgdsl_examples._

object ImageDslInterpTestApp extends App {
  trait TestInterp extends Ex with ImgInterp {
    override def test() = run(res)
  }
  (new Ex1 with TestInterp).test()
  (new Ex2 with TestInterp).test()
  (new Ex3 with TestInterp).test()
  (new Ex4 with TestInterp).test()
  (new Ex5 with TestInterp).test()
  (new Ex6 with TestInterp).test()
}

object ImageDslCompTestApp extends App {
  trait TestComp extends Ex with ImgComp with Impl {
    override def test() = {
      run(res)
      utils.writeFileIndented(s"img$i.c", code)
    }
  }
  (new Ex1 with TestComp).test()
  (new Ex2 with TestComp).test()
  (new Ex3 with TestComp).test()
  (new Ex4 with TestComp).test()
  (new Ex5 with TestComp).test()
  (new Ex6 with TestComp).test()
}
