DEF=ite-bug
EXT=ite
TESTDIR=.
KOMPILE_BACKEND=haskell

%-spec.k %-spec.md: kompile
ifeq ($(TESTDIR),$(RESULTDIR))
	$(KPROVE) $@ $(KPROVE_FLAGS) $(DEBUG) --definition $(DEF)-kompiled $(CONSIDER_ERRORS) $(REMOVE_PATHS) | sed 's!kore-exec: \[[0-9]*\]!kore-exec: []!g' $(CHECK) $@.out
else
	$(KPROVE) $@ $(KPROVE_FLAGS) $(DEBUG) --definition $(DEF)-kompiled $(CONSIDER_ERRORS) $(REMOVE_PATHS) | sed 's!kore-exec: \[[0-9]*\]!kore-exec: []!g' $(CHECK) $(RESULTDIR)/$(notdir $@).out
endif

include ../include/ktest.mak
