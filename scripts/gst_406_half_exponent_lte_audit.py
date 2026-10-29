#!/usr/bin/env python3
"""Independent exact integer audit for the anti-LTE half-exponent GST route.

This is a finite consistency audit, NOT a proof of the all-m or all-K
claims; those require Lean's symbolic recurrence and physical transport.
No random sampling, floating arithmetic, or implicit skipped residue.
"""
MOD=3**9
UNIT=8416
OFFSET=14049

def dmod(m):
    s=pow(2,3**m,3**(m+10))
    assert (s+1)%(3**(m+1))==0
    return ((s+1)//3**(m+1))%MOD

def hit(x,y):
    return next((j for j in range(9) if x//3**j%3==2
                 and y//3**j%3==2),None)

for m in range(8,31):
    assert dmod(m)==UNIT,(m,dmod(m))

# Exact whole modulus-3^9 classification; EVERY u residue included.
hist={j:0 for j in range(9)}
nohit=[]
for u in range(MOD):
    x=(OFFSET+UNIT*u)%MOD
    y=(4*x+1)%MOD
    j=hit(x,y)
    if j is None:nohit.append(u)
    else:hist[j]+=1

assert len(nohit)==4160
assert sum(hist.values())==MOD-4160==15523
assert hit(OFFSET,4*OFFSET+1)==8

# Independently calculate the ORIGINAL powers 4^K by pow(base,exp,mod).
# The quotient is integral because 4^K mod 3^(m+10) ==1 mod3.
for m in [8,9,10,11,12,16,25,50,100]:
    H=(3**m-1)//2
    P=3**(m+10)
    for u in [0,1,2,3,4,13,49,243,19682]:
        k=H+u*3**m
        src=pow(4,k,P)
        nbr=pow(4,k+1,P)
        assert src%3==1 and nbr%3==1
        a=(src-1)//3
        b=(nbr-1)//3
        assert a%(3**m)==H
        assert b%(3**m)==3**m-1
        assert (a//3**m)%MOD==(OFFSET+UNIT*u)%MOD, (m,u,"src")
        assert (b//3**m)%MOD==(4*(OFFSET+UNIT*u)+1)%MOD, (m,u,"nbr")
        expected=hit((OFFSET+UNIT*u)%MOD,(4*(OFFSET+UNIT*u)+1)%MOD)
        physical=next((j for j in range(9)
                       if src//3**(m+1+j)%3==2
                       and nbr//3**(m+1+j)%3==2),None)
        assert physical==expected,(m,u,expected,physical)

print("ANTI_LTE_HALF_EXPONENT_EXACT_AUDIT_PASS=1")
print("d8_mod_3^9=8416;source_tail=14049;neighbor_tail=16831")
print(f"tested_all_multiplier_residues={MOD}")
print(f"common_two_in_first_nine_postprefix_positions={sum(hist.values())}")
print(f"survive_first_nine_postprefix_positions={len(nohit)}")
print("complete_global_hGate_proof=NO")
