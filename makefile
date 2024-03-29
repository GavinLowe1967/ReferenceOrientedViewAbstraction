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

COLLDIR = $(DIR)/collection

COMBINERP = $(DIR)/CombinerP
REMAPPERP = $(DIR)/RemapperP
EXTENDERP = $(DIR)/ExtendabilityP

FSC = fsc -deprecation -cp $(CP)

# all:	$(DIR)/VA.class Instrumentation.class Experiment.class
all:   $(DIR)/VA.class Instrumentation.class $(DIR)/CompileTest.class

clean:
	rm $(DIR)/*.class $(DIR)/*/*.class; fsc -shutdown

# Collections

$(COLLDIR)/MyHashSet.class:	$(COLLDIR)/Sharding.class $(DIR)/package.class

$(COLLDIR)/ShardedHashSet.class:	$(COLLDIR)/MyHashSet.class

$(COLLDIR)/ShardedHashMap.class: $(COLLDIR)/Sharding.class	\
  $(DIR)/package.class $(COLLDIR)/DeletableMap.class

$(COLLDIR)/LockableMap.class: $(COLLDIR)/ShardedHashMap.class

# States etc.

$(DIR)/State.class: $(DIR)/package.class

$(DIR)/StateArray.class: $(DIR)/State.class $(COLLDIR)/ShardedHashSet.class \
  $(DIR)/IdentitiesBitMap.class

$(DIR)/StateMap.class: $(DIR)/State.class

$(DIR)/MyTrieStateMap.class $(DIR)/StateHashMap.class: $(DIR)/StateMap.class

$(DIR)/MyStateMap.class: $(DIR)/MyTrieStateMap.class $(DIR)/StateHashMap.class

$(DIR)/ServerStates.class: $(DIR)/State.class $(COLLDIR)/MyHashMap.class $(DIR)/Pools.class

# FDR interaction

$(DIR)/FDRSession.class: $(DIR)/Concurrency.class

$(DIR)/FDREvents.class:  $(DIR)/Concurrency.class $(DIR)/FDRSession.class  $(DIR)/Pools.class


$(DIR)/FDRTransitionMap.class: $(DIR)/State.class $(DIR)/CSPFileParser.class	\
   $(DIR)/FDREvents.class $(DIR)/MyStateMap.class				\
   $(DIR)/RemapperP/Remapper.class

# Views, etc.

$(DIR)/ServersReducedMap.class: $(DIR)/ServerStates.class


$(DIR)/View.class:  $(DIR)/StateArray.class $(DIR)/ServerStates.class $(COLLDIR)/ShardedHashSet.class

# $(DIR)/MyHashSet.class:  $(DIR)/Sharding.class

$(DIR)/ComponentView0.class: $(DIR)/View.class $(DIR)/IdentitiesBitMap.class	\
  $(COLLDIR)/MyHashSet.class $(DIR)/ServersReducedMap.class			\
  $(COLLDIR)/OpenHashMap.class

$(DIR)/ComponentView.class: $(DIR)/ComponentView0.class 

$(DIR)/TestStates.class: $(DIR)/MyStateMap.class

$(DIR)/RemapperP/Remapper.class: $(COLLDIR)/ShardedHashMap.class $(DIR)/ComponentView.class $(DIR)/MyStateMap.class $(DIR)/Pools.class

$(DIR)/RemapperP/RemapperTest.class: $(DIR)/TestStates.class $(DIR)/RemapperP/Remapper.class $(DIR)/Unification.class

$(COMBINERP)/Combiner.class: $(DIR)/RemapperP/Remapper.class

$(COMBINERP)/CombinerTest.class:  $(DIR)/TestStates.class $(COMBINERP)/Combiner.class 

$(DIR)/Unification.class: $(REMAPPERP)/Remapper.class

$(DIR)/UnificationTest.class: $(DIR)/Unification.class $(DIR)/EffectOnUnification.class 

$(DIR)/RemappingExtender.class: $(DIR)/RemapperP/Remapper.class		\
  $(DIR)/Unification.class $(DIR)/Transition.class $(DIR)/Pools.class	\
  $(DIR)/CompressedCandidatesMap.class

$(DIR)/RemappingExtenderTest.class: $(DIR)/RemappingExtender.class

$(DIR)/SingleRefEffectOnUnification.class: $(DIR)/RemappingExtender.class

$(DIR)/SingleRefEffectOnUnificationTest2.class: $(DIR)/SingleRefEffectOnUnification.class

$(DIR)/SingleRefEffectOnUnificationTest.class: $(DIR)/SingleRefEffectOnUnification.class $(DIR)/SingleRefEffectOnUnificationTest2.class

$(DIR)/Transition.class: $(DIR)/ComponentView.class # $(DIR)/Unification.class 
# $(DIR)/SystemP/System.class

$(DIR)/TransitionSet.class $(DIR)/NewTransitionSet.class: $(DIR)/Transition.class $(DIR)/ComponentView.class $(COLLDIR)/ShardedHashMap.class

$(DIR)/TransitionTemplateSet.class: $(DIR)/ComponentView.class

$(DIR)/ViewSet.class: $(DIR)/ComponentView.class $(COLLDIR)/MyHashSet.class $(DIR)/Transition.class

$(DIR)/IndexSet.class: $(DIR)/ComponentView.class

$(DIR)/NewViewSet.class: $(DIR)/ViewSet.class $(DIR)/IndexSet.class \
  $(COLLDIR)/ShardedHashMap.class $(COLLDIR)/ShardedHashSet.class

# # The system itself

$(DIR)/Components.class: $(DIR)/FDRSession.class	\
  $(DIR)/FDRTransitionMap.class $(DIR)/ComponentView.class

$(DIR)/Servers.class: $(DIR)/FDRSession.class $(COLLDIR)/MyHashMap.class	\
   $(DIR)/FDRTransitionMap.class

$(DIR)/SystemP/System.class: $(DIR)/FDRTransitionMap.class		\
  $(DIR)/Components.class $(DIR)/Servers.class $(DIR)/NewViewSet.class	\
  $(DIR)/IdentitiesBitMap.class

$(DIR)/SystemP/SystemTest.class: $(DIR)/TestStates.class $(DIR)/SystemP/System.class

# # EffectOn and helper modules


$(DIR)/MissingCommon.class: $(DIR)/Unification.class $(DIR)/ViewSet.class	\
  $(COLLDIR)/IntSet.class $(COLLDIR)/KeyedSet.class
# $(COLLDIR)/ShardedHashMap.class

# $(DIR)/MissingInfo.class:  $(DIR)/MissingCommon.class

# $(DIR)/MissingInfoStore.class: $(COLLDIR)/ShardedHashSet.class $(DIR)/MissingInfo.class 

$(DIR)/EffectOnStore.class: $(COLLDIR)/OpenHashSet.class	\
  $(COLLDIR)/ShardedHashMap.class
# $(DIR)/MissingInfoStore.class

# New EffectOn store

$(DIR)/InducedTransitionInfo.class:  $(DIR)/ComponentView.class \
  $(DIR)/Transition.class $(DIR)/SingleRefEffectOnUnification.class

$(DIR)/MissingCrossReferences.class: $(DIR)/InducedTransitionInfo.class \
  $(DIR)/ViewSet.class  $(DIR)/RemappingExtender.class

$(DIR)/SimpleMissingCommon.class: $(DIR)/MissingCommon.class

$(DIR)/TwoStepMissingCommon.class: $(DIR)/MissingCommon.class

$(DIR)/MissingCommonFactory.class: $(DIR)/SimpleMissingCommon.class $(DIR)/TwoStepMissingCommon.class

$(DIR)/MissingCommonWrapper.class: $(DIR)/MissingCommonFactory.class $(DIR)/MissingCrossReferences.class

$(DIR)/NewEffectOnStore.class: $(DIR)/MissingCommonWrapper.class		\
  $(DIR)/SingleRefEffectOnUnification.class $(COLLDIR)/LockableMap.class

$(DIR)/EffectOnUnification.class:  $(DIR)/Unification.class

$(DIR)/EffectOn.class: $(DIR)/EffectOnUnification.class $(DIR)/ViewSet.class $(DIR)/EffectOnStore.class $(DIR)/SystemP/System.class

# $(DIR)/SingleRefEffectOn.class: $(DIR)/EffectOn.class			\
#    $(DIR)/EffectOnStore.class $(DIR)/SingleRefEffectOnUnification.class

$(DIR)/NewEffectOn.class:  $(DIR)/NewEffectOnStore.class $(DIR)/EffectOn.class

# Extending of transition templates

$(DIR)/CompatibleWithCache.class: $(COLLDIR)/ShardedHashMap.class

$(EXTENDERP)/Extendability.class: $(DIR)/Unification.class $(COMBINERP)/Combiner.class  $(DIR)/CompatibleWithCache.class

$(DIR)/ConsistentStateFinder.class: $(DIR)/SystemP/System.class	\
  $(COMBINERP)/Combiner.class

$(EXTENDERP)/ExtendabilityTest.class: $(DIR)/TestStates.class	\
  $(EXTENDERP)/Extendability.class

$(DIR)/TransitionTemplateExtender.class: $(DIR)/Transition.class	\
  $(EXTENDERP)/Extendability.class $(DIR)/TransitionTemplateSet.class	\
  $(DIR)/ConsistentStateFinder.class

# # Checker and main program

$(DIR)/Debugger.class: $(DIR)/SystemP/System.class $(DIR)/EffectOn.class $(DIR)/NewEffectOn.class

$(DIR)/CheckerState.class: $(DIR)/TransitionSet.class			\
  $(DIR)/NewTransitionSet.class $(DIR)/Unification.class		\
  $(DIR)/NewEffectOn.class $(DIR)/TransitionTemplateExtender.class	\
  $(DIR)/NewViewSet.class

$(DIR)/Checker.class: $(DIR)/CheckerState.class $(DIR)/Debugger.class	\
  $(DIR)/Barrier.class $(DIR)/Concurrency.class

$(DIR)/CheckerTest.class: $(DIR)/Checker.class

# $(DIR)/NewViewExtender.class $(DIR)/Debugger.class $(DIR)/Concurrency.class

TESTS = $(DIR)/RemapperP/RemapperTest.class $(COMBINERP)/CombinerTest.class	\
$(DIR)/SystemP/SystemTest.class $(DIR)/CheckerTest.class			\
$(EXTENDERP)/ExtendabilityTest.class $(DIR)/UnificationTest.class		\
$(DIR)/SingleRefEffectOnUnificationTest.class					\
$(DIR)/RemappingExtenderTest.class $(DIR)/RemappingExtenderTest2.class		\
$(DIR)/CompileTest.class

$(DIR)/VA.class:  $(DIR)/Checker.class $(TESTS)

$(TESTS): $(DIR)/TestStates.class $(DIR)/TestUtils.class

# # Standard recipe

# $(DIR)/collection/MyHashSet.class: Collection/MyHashSet.scala
# 	$(FSC) Collection/MyHashSet.scala

$(DIR)/collection/%.class:	Collection/%.scala
	$(FSC) $<

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
