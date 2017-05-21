#!/usr/bin/env python

# preprocessor: add extra imports
# preprocessor: ghc -F -pgmF

import re
import os, sys

module_imports = {
    "Bytes": """
import qualified Specif
import qualified Data.ByteString as BS
    """,
    "Interface": """
import Replication.TwoDiskEnvironment
    """,
    "ReplicatedDisk": """
import Replication.TwoDiskEnvironment
    """,
    "TwoDiskImpl": """
import Replication.Interpreter
import Replication.TwoDiskEnvironment
    """,
    "DiskSize": """
import Replication.TwoDiskEnvironment
    """,
    "ReadWrite": """
import Replication.TwoDiskEnvironment
    """,
    "Recovery": """
import Replication.TwoDiskEnvironment
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
        imports = module_imports.get(module_name)
        if imports:
            out.write(imports)
            out.write("{-# LINE %d \"%s\" #-}\n" % (n, filename))
    line = line.replace('__FILE__', '"%s"' % sys.argv[2])
    line = line.replace('__LINE__', '%d' % n)
    out.write(line)
out.close()
