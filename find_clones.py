#!/usr/bin/env python3
import sys
import os

LANG=sys.argv[1]
#print("hello", LANG);

REPORTS_DIR="_reports"
def good_dir(d):
  return os.path.isdir(os.path.join(".", d)) and not d.startswith('.') and d != LANG and d != REPORTS_DIR

OUT_FILE=f"{REPORTS_DIR}/report.md"
if not os.path.exists("_reports"):
  os.mkdir("_reports")
#os.remove(OUT_FILE)
os.system("find . -iname _build -exec rm -fr {} \;")

for x in [x for x in os.listdir(".") if good_dir(x)]:
  #print(x)
  cmd = f"jscpd --pattern '{LANG}/**/*.ml*' --pattern '{x}/**/*.ml*' -b -r consoleFull --skipLocal > _reports/vs_{x}.txt"
  print(cmd)
  os.system(cmd)

if 1:
  print("Looking for clones in itself");
  cmd = f"jscpd --pattern '{LANG}/**/*.ml*' -b -r consoleFull > _reports/vs_{LANG}.txt"
  os.system(cmd)

os.system(f"echo '#### Результат поиска клонов\n' > jscpd_report.txt")
os.system(f"cat {REPORTS_DIR}/*.txt >> jscpd_report.txt")
