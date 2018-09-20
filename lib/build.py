#!/usr/bin/env python3

from kninja import *
import sys
import os.path

# Helpers
# =======

def test_kfront_to_kore(proj, kdef, testfile):
    out = main.krun( output = kink.builddir(testfile + '.out')
                   , input  = testfile + ''
                   )
    kore = kdef.build( outputs = kink.builddir(testfile + '.kore')
                     , rule = 'kore-from-config'
                     , inputs = out
                     )
    kink.build( outputs = kink.builddir(testfile + '.kore.ast')
              , rule    = 'kore-parser'
              , inputs  = kore
              )
    return main.check_actual_expected(os.path.basename(testfile), kore, testfile + '.expected')

# Project Definition
# ==================

kink = KProject()

# Building Kore & Kore Support
# ----------------------------

### Submodule init update

# TODO: Figure out how to avoid calling `stack build` all the time.
kink.rule( 'kore-parser'
         , description = 'kore-parser'
         , command     = 'stack build kore:exe:kore-parser && stack exec kore-parser $in > $out'
         )
kink.build(kink.extdir('kore', '.git'), 'git-submodule-init')

# Converting Frontend Definitions
# -------------------------------

main = kink.kdefinition( 'kink'
                       , main = kink.tangle('kink.md', kink.tangleddir('kink/kink.k'))
                       , backend = 'java'
                       , alias = 'kink'
                       , kompile_flags = '-I .'
                       )
kink.rule( 'kore-from-config'
         , description = 'Extracting <kore> cell'
         , command = 'lib/kore-from-config $in $out'
         )
test_kfront_to_kore(main, kink, 'foobar/t/foobar.kfront')
