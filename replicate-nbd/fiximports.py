#!/usr/bin/env python

# preprocessor: add extra imports
# preprocessor: ghc -F -pgmF

import re
import os, sys

common_imports = """
import Replication.TwoDiskEnvironment
"""

module_imports = {
    "Bytes": """
import qualified Data.ByteString as BS
    """,
    "TwoDiskImpl": """
import qualified Replication.TwoDiskOps as TD
    """,
}

fs_filename = sys.argv[1]
filename = sys.argv[2]
out = open(sys.argv[3], "w")

module_name = None

MODULE_RE = re.compile("module (?P<module>.*) where\n")

out.write("{-# LINE 1 \"%s\" #-}\n" % (filename))
for n, line in enumerate(open(filename), 1):
    m = MODULE_RE.match(line)
    if m:
        module_name = m.group("module")
    if line.strip() == "import qualified Prelude":
        imports = common_imports
        mod_imports = module_imports.get(module_name)
        if mod_imports:
            imports += "\n" + mod_imports
        out.write(imports)
        out.write("{-# LINE %d \"%s\" #-}\n" % (n, filename))
    line = line.replace('__FILE__', '"%s"' % sys.argv[2])
    line = line.replace('__LINE__', '%d' % n)
    out.write(line)
out.close()
