WARNING: DON'T RUN THE TLC ANALYSIS ON THIS MODEL.

If you don't abort the analysis you'll end up with your CPU maxing out and your
disk or RAM filling up.

---- MODULE Counter ----
EXTENDS Naturals


VARIABLE cnt


Init == cnt = 0


Next == cnt + 1 = cnt'
====
