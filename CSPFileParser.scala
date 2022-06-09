package ViewAbstraction

import scala.collection.mutable.ArrayBuffer

/** Information about components that should be omitted from Views.  
  * @param processName the name of the principal process
  * @param params list of parameters and types for processName
  * @param omit the parameters for which the referred component should be 
  * omitted.
  */ 
case class OmitInfo(
  processName: String, params: List[(String,String)], omit: List[String])

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
  val omitInfos = new ArrayBuffer[OmitInfo]
  var serversName = ""
  var serversRenameName = ""

  init()

  /** Parse annotations in file, extracting variables. */
  private def init() = {
    val source = scala.io.Source.fromFile(fname)
    val lines = source.getLines().toList
    for(line <- lines){
      val start = line.indexOfSlice(tag)
      if(start >= 0){
        val rest = line.drop(start+tag.length).dropWhile(whiteSpace)
        val eqIndex = rest.indexOf('=')
        if(eqIndex < 0){ println("Illegal annotation: "+line); sys.exit() }
        val lhs0 = rest.take(eqIndex); val lhs = lhs0.filter(!whiteSpace(_))
        val rhs0 = rest.drop(eqIndex+1)
        val rhs = rhs0.filter(!whiteSpace(_))
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
          case "omitInfo" => omitInfos += parseOmitInfo(rhs0)
          case _ =>
            println("Annotation variable not recognised: "+lhs0); sys.exit()
        }
      }
    } // end of for loop

    // Check all necessary variables defined. 
    if(serversName.isEmpty && serversRenameName.isEmpty){
      println("Missing definition for servers"); sys.exit()
    }
    if(serversName.nonEmpty && serversRenameName.nonEmpty){
      println("Two definitions for servers"); sys.exit()
    }
    val numFamilies = componentProcessNames.length
    if(componentAlphabets.length != numFamilies ||
         identityTypes.length != numFamilies || 
         componentActives.length != numFamilies){
      println("Inconsistent numbers of definitions for \"component process\",\n"+
                "\"component alphabet\", \"identity type\", "+
                "and \"component active\".")
      sys.exit()
    }
    // Advance componentRenames
    while(componentRenames.length < numFamilies) componentRenames += None

    if(numFamilies == 0){
      println("Missing definitions for \"component process\",\n"+
                "\"component alphabet\" and \"identity type\"")
      sys.exit()
    }
    // if(identityTypes.distinct.length != identityTypes.length){
    //   println("Identity types are not distinct"); sys.exit
    // }
    // numTypes = identityTypes.length
    setNumTypes(identityTypes.distinct.length, identityTypes.length)
  }

  /** Does c represent white space? */
  private def isWhite(c: Char) = c == ' ' || c == '\t'

  /** Drop white space from start and end of st. */
  def dropWhite(st: String) = 
    st.dropWhile(isWhite).reverse.dropWhile(isWhite).reverse

  /** Extract name from st, dropping leading and trailing white space, and
    * checking all characters are alpha-numeric. */
  private def getName(st: String): String = {
    val st1 = dropWhite(st)
    assert(st1.forall(c => c.isLetterOrDigit),
      "Unexpected character in \""+st1+"\"")
    st1
  }

  /** Given a string of the form "name: type", extract name and type. */
  private def extractParam(st: String) = {
    val colonIndex = st.indexOf(':'); assert(colonIndex > 0)
    val name = getName(st.take(colonIndex))
    val theType = getName(st.drop(colonIndex+1))
    (name, theType)
  }

  /** Parse an omitInfo string. */
  private def parseOmitInfo(omitString: String): OmitInfo = {
    // Extract list of omissions
    val omitIndex = omitString.indexOf("omit "); assert(omitIndex >= 0)
    assert(omitString.take(omitIndex).forall(isWhite))
    val fromIndex = omitString.indexOf(" from "); assert(fromIndex > omitIndex)
    val omissionsString = omitString.take(fromIndex).drop(omitIndex+4)
    val omits = omissionsString.split(',').map(getName).toList
    // Extract principal name
    val afterFrom = omitString.drop(fromIndex+5)
    val paramStartIndex = afterFrom.indexOf('(')
    val principalName = getName(afterFrom.take(paramStartIndex))
    // Parameters
    val paramEndIndex = afterFrom.indexOf(')', paramStartIndex+1)
    val paramsString = afterFrom.take(paramEndIndex).drop(paramStartIndex+1)
    val params = paramsString.split(',').toList.map(extractParam)
    // Check all the omits fields are included in params
    for(omit <- omits)
      assert(params.exists(_._1 == omit), 
        s"Omission field $omit not included in parameters $params")
    // Construct result
    val result = OmitInfo(principalName, params, omits)
    println(s"Omit information: $result")
    result
  }


}
