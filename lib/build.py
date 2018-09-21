#!/usr/bin/env python3

from kninja import *
import sys
import os.path

# Helpers
# =======

def test_kfront_to_kore(proj, kdef, testfile):
    out = kdef.krun( output = proj.builddir(testfile + '.out')
                   , input  = testfile + ''
                   )
    kore = proj.build( outputs = proj.builddir(testfile + '.kore')
                     , rule = 'kore-from-config'
                     , inputs = out
                     )
    proj.build( outputs = proj.builddir(testfile + '.kore.ast')
              , rule    = 'kore-parser'
              , inputs  = kore
              )
    return kdef.check_actual_expected(os.path.basename(testfile), kore, testfile + '.expected')

# Project Definition
# ==================

proj = KProject()

# Building Kore & Kore Support
# ----------------------------

### Submodule init update

# TODO: Figure out how to avoid calling `stack build` all the time.
proj.rule( 'kore-parser'
         , description = 'kore-parser'
         , command     = 'stack build kore:exe:kore-parser && stack exec kore-parser $in > $out'
         )
proj.build(proj.extdir('kore', '.git'), 'git-submodule-init')

# Converting Frontend Definitions
# -------------------------------

kink = proj.kdefinition( 'kink'
                       , kink = proj.tangle('kink.md', proj.tangleddir('kink/kink.k'))
                       , backend = 'java'
                       , alias = 'kink'
                       , kompile_flags = '-I .'
                       )
proj.rule( 'kore-from-config'
         , description = 'Extracting <kore> cell'
         , command = 'lib/kore-from-config $in $out'
         )
test_kfront_to_kore(proj, kink, 'foobar/t/foobar.kfront')

