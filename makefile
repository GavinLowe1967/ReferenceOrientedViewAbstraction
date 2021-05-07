# Path to where ox.gavin is stored.
UTIL = /home/gavin/Scala/Util

# Path to the FDR installation 
FDRHOME = /home/gavin/bin/FDRSym/fdr

# Path to the Scala installation
SCALAHOME = /users/gavin/bin/scala/scala-2.13.1

CP = .:$(UTIL):$(FDRHOME)/lib/fdr.jar
# :scala-parallel-collections_2.13-0.2.0.jar

DIR = ViewAbstraction

COMBINERP = $(DIR)/CombinerP
REMAPPERP = $(DIR)/RemapperP
EXTENDERP = $(DIR)/ExtendabilityP

FSC = fsc -deprecation -cp $(CP)

# all:	$(DIR)/VA.class Instrumentation.class Experiment.class
all:   $(DIR)/VA.class

clean:
	rm $(DIR)/*.class $(DIR)/*/*.class; fsc -shutdown

# States etc.

$(DIR)/State.class: $(DIR)/package.class

$(DIR)/StateArray.class: $(DIR)/State.class

$(DIR)/StateMap.class: $(DIR)/State.class $(DIR)/Sharding.class

$(DIR)/MyTrieStateMap.class $(DIR)/StateHashMap.class: $(DIR)/StateMap.class

$(DIR)/MyStateMap.class: $(DIR)/MyTrieStateMap.class $(DIR)/StateHashMap.class

$(DIR)/ServerStates.class: $(DIR)/State.class $(DIR)/MyHashMap.class

# FDR interaction

$(DIR)/FDRSession.class: $(DIR)/Concurrency.class

$(DIR)/FDRTransitionMap.class: $(DIR)/State.class $(DIR)/CSPFileParser.class	\
   $(DIR)/FDRSession.class $(DIR)/MyStateMap.class

# Views, etc.

$(DIR)/View.class: $(DIR)/ServerStates.class $(DIR)/StateArray.class

$(DIR)/TestStates.class: $(DIR)/MyStateMap.class

$(DIR)/RemapperP/Remapper.class: $(DIR)/View.class 

$(DIR)/RemapperP/RemapperTest.class: $(DIR)/TestStates.class $(DIR)/RemapperP/Remapper.class $(DIR)/RemapperP/Unification.class

$(COMBINERP)/Combiner.class: $(DIR)/RemapperP/Remapper.class

$(REMAPPERP)/Unification.class: $(REMAPPERP)/Remapper.class

$(COMBINERP)/CombinerTest.class:  $(DIR)/TestStates.class $(COMBINERP)/Combiner.class 


$(DIR)/TransitionSet.class: $(DIR)/View.class

$(DIR)/TransitionTemplateSet.class: $(DIR)/View.class

$(DIR)/ViewSet.class: $(DIR)/View.class $(DIR)/MyHashSet.class

# # The system itself

$(DIR)/Components.class: $(DIR)/FDRSession.class	\
  $(DIR)/FDRTransitionMap.class $(DIR)/View.class

$(DIR)/Servers.class: $(DIR)/FDRSession.class $(DIR)/MyHashMap.class	\
   $(DIR)/FDRTransitionMap.class

$(DIR)/SystemP/System.class: $(DIR)/FDRTransitionMap.class		\
  $(DIR)/Components.class $(DIR)/Servers.class $(DIR)/ViewSet.class	\
  $(COMBINERP)/Combiner.class

$(DIR)/SystemP/SystemTest.class: $(DIR)/TestStates.class $(DIR)/SystemP/System.class

# # Checker and main program

$(DIR)/CompatibleWithCache.class: $(DIR)/BasicHashMap.class

$(DIR)/Debugger.class: $(DIR)/SystemP/System.class

$(EXTENDERP)/Extendability.class: $(DIR)/RemapperP/Unification.class $(DIR)/CompatibleWithCache.class

$(EXTENDERP)/ExtendabilityTest.class: $(EXTENDERP)/Extendability.class 

$(DIR)/EffectOn.class:  $(DIR)/EffectOnStore.class $(REMAPPERP)/Remapper.class

$(DIR)/Checker.class: $(DIR)/SystemP/System.class $(DIR)/TransitionSet.class $(DIR)/TransitionTemplateSet.class $(DIR)/RemapperP/Unification.class  $(DIR)/Debugger.class  $(DIR)/EffectOn.class $(EXTENDERP)/Extendability.class

$(DIR)/CheckerTest.class: $(DIR)/Checker.class

# $(DIR)/NewViewExtender.class $(DIR)/Debugger.class $(DIR)/Concurrency.class

$(DIR)/VA.class:  $(DIR)/Checker.class $(DIR)/RemapperP/RemapperTest.class $(COMBINERP)/CombinerTest.class $(DIR)/SystemP/SystemTest.class $(DIR)/CheckerTest.class $(EXTENDERP)/ExtendabilityTest.class

# # Standard recipe

$(DIR)/RemapperP/%.class $(DIR)/SystemP/%.class $(COMBINERP)/%.class $(EXTENDERP)/%.class:	%.scala
	$(FSC) $<

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
