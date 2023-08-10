import os

cwd = os.getcwd()

print("STAGING_AREA=" + cwd.replace("\\", "/").replace("C:", ""))
