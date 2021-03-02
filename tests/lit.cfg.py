# -*- Python -*-

from lit.llvm import llvm_config
import lit.formats

config.name = 'llvm-mutate'
config.test_format = lit.formats.ShTest(True)

config.suffixed = ['.ll']