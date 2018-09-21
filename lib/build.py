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
    kdef.check_actual_expected(os.path.basename(testfile), kore, testfile + '.expected')
    return kore

# Project Definition
# ==================

proj = KProject()

# Building Kore & Kore Support
# ----------------------------

### Submodule init update

# TODO: Figure out how to avoid calling `stack build` all the time.
proj.rule( 'kore-parser'
         , description = 'kore-parser'
         , command     = 'stack build kore:exe:kore-parser && stack exec -- kore-parser $in > $out'
         )
proj.rule( 'kore-exec'
         , description = 'kore-exec'
         , command     = 'stack build kore:exe:kore-exec && stack exec -- kore-exec $kore --module FOOBAR --pattern $in > $out'
         )
proj.build(proj.extdir('kore', '.git'), 'git-submodule-init')

# Converting Frontend Definitions
# -------------------------------

kink = proj.kdefinition( 'kink'
                       , main = proj.tangle('kink.md', proj.tangleddir('kink/kink.k'))
                       , backend = 'java'
                       , alias = 'kink'
                       , kompile_flags = '-I .'
                       )
proj.rule( 'kore-from-config'
         , description = 'Extracting <kore> cell'
         , command = 'lib/kore-from-config $in $out'
         )
foobar_kore = test_kfront_to_kore(proj, kink, 'foobar/t/foobar.kfront')

# Building and running definitions using the K5/Java translation
# --------------------------------------------------------------

foobar_k5 = proj.kdefinition( 'foobar-k5'
                            , main = 'foobar/foobar.k'
                            , backend = 'kore'
                            , alias = 'foobar-k5'
                            , kompile_flags = '--syntax-module FOOBAR'
                            )
bar_kast = foobar_k5.kast( output = proj.builddir('foobar/programs/bar.foobar.kast')
                         , input  =               'foobar/programs/bar.foobar'
                         , kast_flags = '--kore'
                         )
out = proj.build( inputs  = bar_kast
                , rule    = 'kore-exec'
                , outputs = proj.builddir('foobar/programs/bar.foobar.kink.out')
                , implicit = foobar_kore
                , variables = { 'kore' : foobar_kore
                              }
                )
foobar_k5.check_actual_expected('foobar/programs/bar.foobar.kink', out, 'foobar/programs/bar.foobar.expected')

out = proj.build( inputs  = bar_kast
                , rule    = 'kore-exec'
                , outputs = proj.builddir('foobar/programs/bar.foobar.k5.out')
                , implicit = 'foobar/foobar.handwritten.kore'
                , variables = { 'kore' : 'foobar/foobar.handwritten.kore'
                              }
                )
foobar_k5.check_actual_expected('foobar/programs/bar.foobar.handwritten', out, 'foobar/programs/bar.foobar.expected')
