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
                       )
main.krun_and_check( output_dir   = kink.builddir('foobar/t')
                   , input    = 'foobar/t/foobar.kfront'
                   , expected = 'foobar/t/foobar.kfront.expected'
                   )

