package lms.verify

import java.io._
import org.scalatest.FunSuite
import utils._

trait TestSuite extends FunSuite {
  def write(label: String, code: String, suffix: String = "c") = {
    val name = label+".actual."+suffix
    writeFileIndented(name, code)
  }
}
