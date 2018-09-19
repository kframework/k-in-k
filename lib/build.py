#!/usr/bin/env python3

from kninja import *
import sys

# Helpers
#
class KinK(KProject):
    def __init__(self):
        super().__init__(builddir = '.build', k_repo = "ext/k")
        self.testdir = '$builddir/t/'

kink = KinK()

