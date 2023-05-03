


############
import sys
print("Checking python version")
print(sys.version)
assert sys.version_info[0:3] == (3, 9, 15)

import platform
assert platform.python_version_tuple() == ('3', '9', '15')


print("Checking z3 import")
import z3

