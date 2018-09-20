#!/usr/bin/env python3

from kninja import *
import sys

# Helpers
#
kink = KProject()
main = kink.kdefinition( 'kink'
                       , main = kink.tangle('kink.md', kink.tangleddir('kink/kink.k'))
                       , backend = 'java'
                       , alias = 'kink'
                       , kompile_flags = '-I .'
                       )

# Converting Frontend Definitions
# ===============================

kink.rule( 'kore-from-config'
         , description = 'Extracting <kore> cell'
         , command = 'lib/kore-from-config $in $out'
         )

fb_out = main.krun( output = kink.builddir('foobar/t/foobar.kfront.out')
                  , input  = 'foobar/t/foobar.kfront'
                  )
kore = kink.build( outputs = kink.builddir('foobar/t/foobar.kfront.kore')
                 , rule = 'kore-from-config'
                 , inputs = fb_out
                 )
main.check_actual_expected('foobar.kfront.kore', kore, 'foobar/t/foobar.kfront.expected')
