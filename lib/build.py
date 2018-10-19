#!/usr/bin/env python3

from kninja import *
import sys
import os.path

# Project Definition
# ==================

proj = KProject()
proj.build_ocaml()
proj.build(proj.extdir('kore', '.git'), 'git-submodule-init')

# Non-standard rules needed for K in K
# ------------------------------------

kore_from_config = proj.rule( 'kore-from-config'
                            , description = 'Extracting <kore> cell'
                            , command = 'lib/kore-from-config $in $out'
                            , ext = 'kore'
                            )
kore_parser = proj.rule( 'kore-parser'
                       , description = 'kore-parser'
                       , command     = 'stack build kore:exe:kore-parser && stack exec -- kore-parser $in > $out'
                       )
def kore_exec(kore, ext = 'kore-exec'):
    return proj.rule( 'kore-exec'
                    , description = 'kore-exec'
                    , command     = 'stack build kore:exe:kore-exec && stack exec -- kore-exec $kore --module FOOBAR --pattern $in > $out'
                    ) \
                    .variables(kore = kore) \
                    .implicit(kore)


# -----------------------------------------------------------------------------

ekore = proj.source('ekore.md') \
            .then(proj.tangle().output(proj.tangleddir('ekore.k'))) \
            .then(proj.kompile()
                        .implicit(proj.source('kore.k'))
                        .variables( backend = 'java'
                                  , directory = proj.builddir('ekore')
                                  , flags = '-I .'
                                  ))
proj.source('imp/imp.ekore0') \
    .then(ekore.krun())
proj.source('foobar/foobar.ekore0') \
    .then(ekore.krun())
proj.source('imp/imp.ekore1') \
    .then(ekore.krun())
proj.source('foobar/foobar.ekore1') \
    .then(ekore.krun())

# Probably needs to be removed?
# =============================

# Converting Frontend Definitions
# -------------------------------

kink = proj.source('kink.md') \
           .then(proj.tangle().output(proj.tangleddir('kink.k'))) \
           .then(proj.kompile().variables(backend = 'ocaml', flags = '-I .', directory = proj.builddir('kink'))) \
           .alias('kink')

def translate_with_kink(testfile):
    kore = testfile.then(kink.krun()) \
                   .then(kore_from_config)
    kore.then(kore_parser.output(proj.builddir(testfile.path + '.kore.ast')))
    kore.then(proj.check(testfile.path + '.expected'))
    return kore

# Foobar
# ------

foobar_kink = translate_with_kink(proj.source('foobar/foobar.kfront'))

# Build the foobar definition using K5.
#
foobar_k5 = proj.source('foobar/foobar.k') \
                .then(proj.kompile().variables( directory = proj.builddir('foobar')
                                              , backend = 'kore'
                                              , flags = '--syntax-module FOOBAR'
                     )                        ) \
# Use the K5 definition to convert foobar programs to kast format
bar_kast = proj.source('foobar/programs/bar.foobar') \
               .then(foobar_k5.kast().variables(flags = '--kore'))
bar_kast.then(kore_exec(foobar_kink).ext('kink.kore-exec')) \
        .then(proj.check('foobar/programs/bar.foobar.expected')) \
        .default()
bar_kast.then(kore_exec(proj.source('foobar/foobar.handwritten.kore')).ext('handwriten.kore-exec')) \
        .then(proj.check(proj.source('foobar/programs/bar.foobar.expected'))) \
        .default()
