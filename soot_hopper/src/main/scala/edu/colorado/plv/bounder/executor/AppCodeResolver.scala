package edu.colorado.plv.bounder.executor

import edu.colorado.plv.bounder.ir.JimpleWrapper
import edu.colorado.plv.bounder.ir.JimpleWrapper.getClass

import scala.io.Source
import scala.util.matching.Regex

trait AppCodeResolver {
  def isFrameworkClass(packageName:String):Boolean
  def isCallin(packageName:String, methodName:String):Boolean
  def getCallback(packageName:String, methodName:String): (String,String)
}

class DefaultAppCodeResolver () extends AppCodeResolver {
  protected val frameworkExtPath = getClass.getResource("/FrameworkExtensions.txt").getPath
  protected val extensionStrings: Regex = Source.fromFile(frameworkExtPath).getLines.mkString("|").r
  def isFrameworkClass(packageName:String):Boolean = packageName match{
    case extensionStrings() => true
    case _ => false
  }

  override def isCallin(packageName: String, methodName: String): Boolean = ???

  override def getCallback(packageName: String, methodName: String): (String, String) = ???
}