#!/usr/bin/env python3

from kninja import *
import sys
import os.path

# Project Definition
# ==================

proj = KProject()
proj.build(proj.extdir('kore', '.git'), 'git-submodule-init')

# Non-standard rules needed for K in K
# ------------------------------------

kore_from_config = proj.rule( 'kore-from-config'
                            , description = 'Extracting <kore> cell'
                            , command = 'lib/kore-from-config $cell $in $out'
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

# Kore to K Pipeline
# ------------------

ekore = proj.source('ekore.md') \
            .then(proj.tangle().output(proj.tangleddir('ekore.k')))
kore = proj.source('kore.k')
kink = proj.source('kink.md') \
           .then(proj.tangle().output(proj.tangleddir('kink.k'))) \
           .then(proj.kompile()
                        .implicit([kore, ekore])
                        .variables( backend = 'java'
                                  , directory = proj.builddir('kink')
                                  , flags = '-I . --syntax-module EKORE-SYNTAX'
                                  ))

def testdir(*paths):
    return os.path.join('t', *paths)

def run_kink(pipeline = '#ekorePipeline'):
    return kink.krun().variables(flags = '"-cPIPELINE=%s"' %(pipeline))

def definition_test(definition, file):
    proj.source(testdir(definition, file)) \
        .then(run_kink()) \
        .then(kore_from_config.variables(cell = 'k')) \
        .then(proj.check(proj.source(testdir(definition, definition + '.ekore.expected')))
                     .variables(flags = '--ignore-all-space')) \
        .default()

# EKore Transformations
ekore_transformations = [ 'frontend-modules.ekore' \
                        , 'declare-sorts.ekore' \
                        , 'declare-symbols.ekore' \
                        ]

# Test each tranformation for given definition, and identity on expected definition
def transformations_tests(definition):
    for transformation in ekore_transformations:
        definition_test(definition, definition + '-' + transformation)

    definition_test(definition, definition + '.ekore.expected')

# Foobar Tests
transformations_tests('foobar')

# Peano Tests
transformations_tests('peano')

# These tests are to make sure we can still parse IMP
proj.source('imp/imp.ekore0').then(run_kink()).default()
proj.source('imp/imp.ekore1').then(run_kink()).default()

# Run programs against generated kore definitions
# -----------------------------------------------

foobar_kore =  proj.source('t/foobar/foobar.ekore.expected') \
                   .then(run_kink(pipeline = '#runWithHaskellBackendPipeline') \
                           .ext('noFrontend')) \
                   .then(kore_from_config) \
                   .default()

