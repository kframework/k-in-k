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
                            , command = 'lib/kore-from-config "$cell" "$in" "$out"'
                            , ext = 'kore'
                            )
kore_parser = proj.rule( 'kore-parser'
                       , description = 'kore-parser'
                       , command     = 'stack build kore:exe:kore-parser && stack exec -- kore-parser $in > $out'
                       )
def kore_exec(kore, ext = 'kore-exec'):
    return proj.rule( 'kore-exec'
                    , description = 'kore-exec'
                    , command     = 'stack build kore:exe:kore-exec && stack exec -- kore-exec $kore --module "$module" --pattern $in > $out'
                    ) \
                    .variables(kore = kore) \
                    .implicit([kore])

# Kore to K Pipeline
# ------------------

ekore = proj.source('ekore.md') \
            .then(proj.tangle().output(proj.tangleddir('ekore.k')))
kore = proj.source('kore.k')
kink = proj.source('kink.md') \
           .then(proj.tangle().output(proj.tangleddir('kink.k'))) \
           .then(proj.kompile(backend = 'java')
                        .implicit([kore, ekore])
                        .variables( directory = proj.builddir('kink')
                                  , flags = '-I . --syntax-module EKORE-SYNTAX'
                                  ))

def testdir(*paths):
    return os.path.join('t', *paths)

def run_kink(pipeline = '#ekorePipeline'):
    return kink.krun().variables(flags = '"-cPIPELINE=%s"' %(pipeline))

def kink_test(base_dir, test_file):
    input = os.path.join(base_dir, test_file)
    expected = os.path.join(base_dir, 'expected.ekore')
    return proj.source(input) \
               .then(run_kink()) \
               .then(kore_from_config.variables(cell = 'k')) \
               .then(proj.check(proj.source(expected))
                            .variables(flags = '--ignore-all-space')) \
               .default()

def lang_test(base_dir, module, program):
    language_kore    = os.path.join(base_dir, 'expected.ekore')
    program_pattern  = os.path.join(base_dir, 'programs', program + '.kast')
    expected_pattern = os.path.join(base_dir, 'programs', program + '.expected')

    lang_no_frontend_kore =  proj.source(language_kore) \
                                 .then(run_kink(pipeline = '#runWithHaskellBackendPipeline') \
                                          .ext('noFrontend')) \
                                 .then(kore_from_config.variables(cell = 'k'))
    return proj.source(program_pattern).then(kore_exec(lang_no_frontend_kore)
                                                 .ext('kore-exec')
                                                 .variables(module = module)
                                            ) \
                                       .then(proj.check(expected_pattern)) \
                                       .default()

# Foobar
foobar_tests = []
foobar_tests += [ kink_test('t/foobar', 'expected.ekore')                 ]
foobar_tests += [ kink_test('t/foobar', 'frontend-modules.ekore')         ]
foobar_tests += [ kink_test('t/foobar', 'declare-sorts.ekore')            ]
foobar_tests += [ kink_test('t/foobar', 'declare-symbols.ekore')          ]
foobar_tests += [ lang_test('t/foobar', 'FOOBAR', 'bar.foobar')           ]
proj.build('t/foobar', 'phony', inputs = Target.to_paths(foobar_tests)) 

# Peano
peano_tests = []
peano_tests += [ kink_test('t/peano', 'expected.ekore')         ]
peano_tests += [ kink_test('t/peano', 'frontend-modules.ekore') ]
peano_tests += [ kink_test('t/peano', 'declare-sorts.ekore')    ]
peano_tests += [ kink_test('t/peano', 'declare-symbols.ekore')  ]
proj.build('t/peano', 'phony', inputs = Target.to_paths(peano_tests)) 

# Imp : make sure we can parse IMP
proj.source('imp/imp.ekore0').then(run_kink(pipeline = '#nullPipeline')).default()
proj.source('imp/imp.ekore1').then(run_kink(pipeline = '#nullPipeline')).default()

# Unit tests
# ==========

proj.source('unit-tests.md') \
    .then(proj.tangle().output(proj.tangleddir('unit-tests-spec.k'))) \
    .then(kink.kprove()) \
    .alias('unit-tests')
