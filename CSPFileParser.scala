package ViewAbstraction

import scala.collection.mutable.ArrayBuffer

class CSPFileParser(fname: String){
  /** Tag used to tag annotation in file. */
  private val tag = "@VA"

  /** Does c represent white space? */
  private def whiteSpace(c: Char) = c == ' ' || c == '\t' || c == '\n'

  /** Numbers of symmetric types. */
  // var numTypes = -1

  // Strings extracted from annotations in the CSP file
  val componentProcessNames = new ArrayBuffer[String]
  val componentAlphabets = new ArrayBuffer[String]
  val identityTypes = new ArrayBuffer[String]
  val componentRenames = new ArrayBuffer[Option[String]]
  val componentActives = new ArrayBuffer[Boolean]
  var serversName = ""
  var serversRenameName = ""

  init()

  /** Parse annotations in file, extracting variables. */
  private def init() = {
    val source = scala.io.Source.fromFile(fname)
    val lines = source.getLines.toList
    for(line <- lines){
      val start = line.indexOfSlice(tag)
      if(start >= 0){
        val rest = line.drop(start+tag.length).dropWhile(whiteSpace)
        val eqIndex = rest.indexOf('=')
        if(eqIndex < 0){ println("Illegal annotation: "+line); sys.exit }
        val lhs0 = rest.take(eqIndex); val lhs = lhs0.filter(!whiteSpace(_))
        val rhs = rest.drop(eqIndex+1).filter(!whiteSpace(_))
        lhs.filter(_.isLetter) match{
          case "componentprocess" => componentProcessNames += rhs
          case "componentalphabet" => componentAlphabets += rhs
          case "componentidentitytype" =>
            identityTypes += rhs
          case "componentrename" =>
            // Advance componentRenames.  We assume that the items for each
            // family are grouped together in the file, and that the rename
            // relation is not the first item relating to this family.  IMPROVE
            val len = (
              componentProcessNames.length max componentAlphabets.length max
                identityTypes.length)
            while(componentRenames.length < len-1) componentRenames += None
            componentRenames += Some(rhs)
            assert(componentRenames.length == len)
          case "componentactive" =>
            val active = rhs.toBoolean; componentActives += active
            println(s"active = $active")
          case "servers" => serversName = rhs
          case "serversRename" => serversRenameName = rhs
          case _ =>
            println("Annotation variable not recognised: "+lhs0); sys.exit
        }
      }
    } // end of for loop

    // Check all necessary variables defined. 
    if(serversName.isEmpty && serversRenameName.isEmpty){
      println("Missing definition for servers"); sys.exit
    }
    if(serversName.nonEmpty && serversRenameName.nonEmpty){
      println("Two definitions for servers"); sys.exit
    }
    val numFamilies = componentProcessNames.length
    if(componentAlphabets.length != numFamilies ||
         identityTypes.length != numFamilies){
      println("Inconsistent numbers of definitions for \"component process\",\n"+
                "\"component alphabet\" and \"identity type\"")
      sys.exit
    }
    // Advance componentRenames
    while(componentRenames.length < numFamilies) componentRenames += None

    if(numFamilies == 0){
      println("Missing definitions for \"component process\",\n"+
                "\"component alphabet\" and \"identity type\"")
      sys.exit
    }
    // if(identityTypes.distinct.length != identityTypes.length){
    //   println("Identity types are not distinct"); sys.exit
    // }
    // numTypes = identityTypes.length
    setNumTypes(identityTypes.distinct.length, identityTypes.length)
  }


}
