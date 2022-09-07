HOME = /home/gavin

# Path to where ox.gavin is stored.
UTIL = $(HOME)/Scala/Util

# Path to the FDR installation 
FDRHOME = /home/gavin/bin/FDRSym/fdr

# Path to the Scala installation
#SCALAHOME = /users/gavin/bin/scala/scala-2.13.1

CP = .:$(UTIL):$(FDRHOME)/lib/fdr.jar
# :scala-parallel-collections_2.13-0.2.0.jar

DIR = ViewAbstraction

COMBINERP = $(DIR)/CombinerP
REMAPPERP = $(DIR)/RemapperP
EXTENDERP = $(DIR)/ExtendabilityP

FSC = fsc -deprecation -cp $(CP)

# all:	$(DIR)/VA.class Instrumentation.class Experiment.class
all:   $(DIR)/VA.class Instrumentation.class $(DIR)/CompileTest.class

clean:
	rm $(DIR)/*.class $(DIR)/*/*.class; fsc -shutdown

# States etc.

$(DIR)/State.class: $(DIR)/package.class

$(DIR)/StateArray.class: $(DIR)/State.class

$(DIR)/StateMap.class: $(DIR)/State.class

$(DIR)/MyTrieStateMap.class $(DIR)/StateHashMap.class: $(DIR)/StateMap.class

$(DIR)/MyStateMap.class: $(DIR)/MyTrieStateMap.class $(DIR)/StateHashMap.class

$(DIR)/ServerStates.class: $(DIR)/State.class $(DIR)/MyHashMap.class

# FDR interaction

$(DIR)/FDRSession.class: $(DIR)/Concurrency.class

$(DIR)/FDREvents.class:  $(DIR)/Concurrency.class $(DIR)/FDRSession.class

$(DIR)/FDRTransitionMap.class: $(DIR)/State.class $(DIR)/CSPFileParser.class	\
   $(DIR)/FDREvents.class $(DIR)/MyStateMap.class				\
   $(DIR)/RemapperP/Remapper.class

# Views, etc.

$(DIR)/ServersReducedMap.class: $(DIR)/ServerStates.class

$(DIR)/View.class:  $(DIR)/StateArray.class $(DIR)/ServerStates.class $(DIR)/ShardedHashSet.class

$(DIR)/MyHashSet.class:  $(DIR)/Sharding.class

$(DIR)/ComponentView0.class: $(DIR)/View.class $(DIR)/MyHashSet.class $(DIR)/ServersReducedMap.class

$(DIR)/ComponentView.class: $(DIR)/ComponentView0.class

$(DIR)/TestStates.class: $(DIR)/MyStateMap.class

$(DIR)/RemapperP/Remapper.class: $(DIR)/ComponentView.class $(DIR)/MyStateMap.class

$(DIR)/RemapperP/RemapperTest.class: $(DIR)/TestStates.class $(DIR)/RemapperP/Remapper.class $(DIR)/Unification.class

$(COMBINERP)/Combiner.class: $(DIR)/RemapperP/Remapper.class

$(COMBINERP)/CombinerTest.class:  $(DIR)/TestStates.class $(COMBINERP)/Combiner.class 

$(DIR)/Unification.class: $(REMAPPERP)/Remapper.class

$(DIR)/UnificationTest.class: $(DIR)/Unification.class $(DIR)/EffectOnUnification.class 

$(DIR)/RemappingExtender.class: $(DIR)/RemapperP/Remapper.class $(DIR)/Unification.class $(DIR)/Transition.class

$(DIR)/RemappingExtenderTest.class: $(DIR)/RemappingExtender.class

$(DIR)/SingleRefEffectOnUnification.class: $(DIR)/RemappingExtender.class

$(DIR)/SingleRefEffectOnUnificationTest2.class: $(DIR)/SingleRefEffectOnUnification.class

$(DIR)/SingleRefEffectOnUnificationTest.class: $(DIR)/SingleRefEffectOnUnification.class $(DIR)/SingleRefEffectOnUnificationTest2.class

$(DIR)/Transition.class: $(DIR)/Unification.class 
# $(DIR)/SystemP/System.class

$(DIR)/TransitionSet.class $(DIR)/NewTransitionSet.class: $(DIR)/Transition.class $(DIR)/ComponentView.class

$(DIR)/TransitionTemplateSet.class: $(DIR)/ComponentView.class

$(DIR)/ViewSet.class: $(DIR)/ComponentView.class $(DIR)/MyHashSet.class $(DIR)/Transition.class

$(DIR)/IndexSet.class: $(DIR)/ComponentView.class

$(DIR)/NewViewSet.class: $(DIR)/ViewSet.class $(DIR)/IndexSet.class \
  $(DIR)/ShardedHashMap.class $(DIR)/ShardedHashSet.class

# # The system itself

$(DIR)/Components.class: $(DIR)/FDRSession.class	\
  $(DIR)/FDRTransitionMap.class $(DIR)/ComponentView.class

$(DIR)/Servers.class: $(DIR)/FDRSession.class $(DIR)/MyHashMap.class	\
   $(DIR)/FDRTransitionMap.class

$(DIR)/SystemP/System.class: $(DIR)/FDRTransitionMap.class		\
  $(DIR)/Components.class $(DIR)/Servers.class $(DIR)/NewViewSet.class

$(DIR)/SystemP/SystemTest.class: $(DIR)/TestStates.class $(DIR)/SystemP/System.class

# # EffectOn and helper modules

$(DIR)/ShardedHashMap.class: $(DIR)/Sharding.class

$(DIR)/MissingCommon.class: $(DIR)/Unification.class $(DIR)/ViewSet.class $(DIR)/ShardedHashMap.class

$(DIR)/MissingInfo.class:  $(DIR)/MissingCommon.class

$(DIR)/MissingInfoStore.class: $(DIR)/ShardedHashSet.class $(DIR)/MissingInfo.class 

$(DIR)/EffectOnStore.class: $(DIR)/MissingInfoStore.class 

$(DIR)/EffectOnUnification.class:  $(DIR)/Unification.class

$(DIR)/EffectOn.class: $(DIR)/EffectOnStore.class				\
  $(DIR)/EffectOnUnification.class $(DIR)/SingleRefEffectOnUnification.class

# Extending of transition templates

$(DIR)/CompatibleWithCache.class: $(DIR)/BasicHashMap.class

$(EXTENDERP)/Extendability.class: $(DIR)/Unification.class $(COMBINERP)/Combiner.class  $(DIR)/CompatibleWithCache.class

$(DIR)/ConsistentStateFinder.class: $(DIR)/SystemP/System.class	\
  $(COMBINERP)/Combiner.class

$(EXTENDERP)/ExtendabilityTest.class: $(DIR)/TestStates.class	\
  $(EXTENDERP)/Extendability.class

$(DIR)/TransitionTemplateExtender.class: $(DIR)/Transition.class	\
  $(EXTENDERP)/Extendability.class $(DIR)/TransitionTemplateSet.class	\
  $(DIR)/ConsistentStateFinder.class

# # Checker and main program

$(DIR)/Debugger.class: $(DIR)/SystemP/System.class

$(DIR)/Checker.class: $(DIR)/TransitionSet.class		\
  $(DIR)/NewTransitionSet.class $(DIR)/Unification.class	\
  $(DIR)/Debugger.class $(DIR)/EffectOn.class			\
  $(DIR)/TransitionTemplateExtender.class $(DIR)/Barrier.class	\
  $(DIR)/Concurrency.class

$(DIR)/CheckerTest.class: $(DIR)/Checker.class

# $(DIR)/NewViewExtender.class $(DIR)/Debugger.class $(DIR)/Concurrency.class

TESTS = $(DIR)/RemapperP/RemapperTest.class $(COMBINERP)/CombinerTest.class	\
$(DIR)/SystemP/SystemTest.class $(DIR)/CheckerTest.class			\
$(EXTENDERP)/ExtendabilityTest.class $(DIR)/UnificationTest.class		\
$(DIR)/SingleRefEffectOnUnificationTest.class					\
$(DIR)/RemappingExtenderTest.class $(DIR)/CompileTest.class

$(DIR)/VA.class:  $(DIR)/Checker.class $(TESTS)

$(TESTS): $(DIR)/TestStates.class $(DIR)/TestUtils.class

# # Standard recipe

$(DIR)/RemapperP/%.class $(DIR)/SystemP/%.class $(COMBINERP)/%.class $(EXTENDERP)/%.class:	%.scala
	$(FSC) $<

$(DIR)/%.class:     %.scala
	$(FSC) $<

# # Experiment

# EXPCLASSPATH = $(CLASSPATH):/users/gavinl/Scala/Util

# Experiment.class: Experiment.scala
# 	$(FSC) Experiment.scala

# Instrumentation

ScalaInstrumentation.class: ScalaInstrumentation.scala $(DIR)/VA.class
	$(FSC) ScalaInstrumentation.scala

ICP = .:$(UTIL)
# :$(SCALAHOME)/lib/scala-library.jar

Instrumentation.class: Instrumentation.java ScalaInstrumentation.class 
	javac -cp $(ICP) Instrumentation.java
