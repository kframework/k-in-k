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
    main.check_actual_expected(os.path.basename(testfile), kore, testfile + '.expected')

# Project Definition
# ==================

kink = KProject()
main = kink.kdefinition( 'kink'
                       , main = kink.tangle('kink.md', kink.tangleddir('kink/kink.k'))
                       , backend = 'java'
                       , alias = 'kink'
                       , kompile_flags = '-I .'
                       )

# Converting Frontend Definitions
# -------------------------------

kink.rule( 'kore-from-config'
         , description = 'Extracting <kore> cell'
         , command = 'lib/kore-from-config $in $out'
         )
test_kfront_to_kore(main, kink, 'foobar/t/foobar.kfront')

