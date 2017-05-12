#!/usr/bin/env python

# preprocessor: add extra imports
# preprocessor: ghc -F -pgmF

import os, sys

imports = """
import qualified Specif
import qualified Data.ByteString as BS
import Utils.Coq
"""

fs_filename = sys.argv[1]
filename = sys.argv[2]
out = open(sys.argv[3], "w")

out.write("{-# LINE 1 \"%s\" #-}\n" % (filename))
for n, line in enumerate(open(filename), 1):
	if (line.strip() == "import qualified Prelude" and
                fs_filename == "src/Bytes.hs"):
		out.write(imports)
		out.write("{-# LINE %d \"%s\" #-}\n" % (n, filename))
	line = line.replace('__FILE__', '"%s"' % sys.argv[2])
	line = line.replace('__LINE__', '%d' % n)
	out.write(line)
out.close()
