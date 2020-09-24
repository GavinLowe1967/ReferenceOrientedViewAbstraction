# Path to where ox.gavin is stored.
UTIL = /home/gavin/Scala/Util

# Path to the FDR installation 
FDRHOME = /home/gavin/bin/FDRSym/fdr

# Path to the Scala installation
SCALAHOME = /users/gavin/bin/scala/scala-2.13.1

CP = .:$(UTIL):$(FDRHOME)/lib/fdr.jar
# :scala-parallel-collections_2.13-0.2.0.jar

DIR = ViewAbstraction

FSC = fsc -deprecation -cp $(CP)

# all:	$(DIR)/VA.class Instrumentation.class Experiment.class
all:  $(DIR)/MyStateMap.class $(DIR)/VA.class $(DIR)/Remapper.class

clean:
	rm *.class $(DIR)/*.class; fsc -shutdown

# $(DIR)/MyHashSet.class $(DIR)/ConcBuffer.class: $(DIR)/Sharding.class

$(DIR)/State.class: $(DIR)/package.class

$(DIR)/StateMap.class: $(DIR)/State.class $(DIR)/Sharding.class

$(DIR)/MyTrieStateMap.class $(DIR)/StateHashMap.class: $(DIR)/StateMap.class

$(DIR)/MyStateMap.class: $(DIR)/MyTrieStateMap.class $(DIR)/StateHashMap.class

$(DIR)/ServerStates.class: $(DIR)/State.class $(DIR)/MyHashMap.class

# $(DIR)/SystemView.class $(DIR)/SystemViewSet.class: SystemView.scala	\
#   SystemViewSet.scala $(DIR)/Views.class $(DIR)/MyHashSet.class		\
#   $(DIR)/ServerStates.class $(DIR)/ConcBuffer.class $(DIR)/Remapper.class
# 	$(FSC) SystemView.scala SystemViewSet.scala

# $(DIR)/SubSystemView.class: $(DIR)/State.class

# $(DIR)/ExtenderMap.class: $(DIR)/SubSystemView.class $(DIR)/Sharding.class

# $(DIR)/NewViewExtender.class: $(DIR)/Remapper.class $(DIR)/SystemView.class	\
#   $(DIR)/SystemViewSet.class $(DIR)/ConcBuffer.class $(DIR)/ExtenderMap.class

# # To create the system using FDR, we need the following classpath

$(DIR)/FDRSession.class: $(DIR)/Concurrency.class

$(DIR)/FDRTransitionMap.class: $(DIR)/State.class $(DIR)/CSPFileParser.class	\
   $(DIR)/FDRSession.class

# # The system itself

$(DIR)/View.class: $(DIR)/ServerStates.class

$(DIR)/Remapper.class: $(DIR)/View.class

$(DIR)/TransitionSet.class: $(DIR)/View.class

$(DIR)/ViewSet.class: $(DIR)/View.class $(DIR)/MyHashSet.class

$(DIR)/Components.class: $(DIR)/FDRSession.class	\
  $(DIR)/FDRTransitionMap.class $(DIR)/View.class

$(DIR)/Servers.class: $(DIR)/FDRSession.class $(DIR)/MyHashMap.class	\
   $(DIR)/FDRTransitionMap.class

$(DIR)/System.class: $(DIR)/FDRTransitionMap.class $(DIR)/Components.class	\
    $(DIR)/Servers.class $(DIR)/ViewSet.class $(DIR)/Remapper.class
# $(DIR)/NewViewExtender.class	\
#    $(DIR)/SystemView.class

# # Checker and main program

# $(DIR)/Debugger.class: $(DIR)/System.class

$(DIR)/Checker.class: $(DIR)/System.class $(DIR)/TransitionSet.class
# $(DIR)/NewViewExtender.class $(DIR)/Debugger.class $(DIR)/Concurrency.class

$(DIR)/VA.class: $(DIR)/System.class $(DIR)/Checker.class

# # Standard recipe

$(DIR)/%.class:     %.scala
	$(FSC) $<

# # Experiment

# EXPCLASSPATH = $(CLASSPATH):/users/gavinl/Scala/Util

# Experiment.class: Experiment.scala
# 	$(FSC) Experiment.scala

# # Instrumentation

# ScalaInstrumentation.class: ScalaInstrumentation.scala
# 	$(FSC) ScalaInstrumentation.scala

# ICP = .:$(UTIL):$(SCALAHOME)/lib/scala-library.jar

# Instrumentation.class: Instrumentation.java ScalaInstrumentation.class
# 	javac -cp $(ICP) Instrumentation.java
