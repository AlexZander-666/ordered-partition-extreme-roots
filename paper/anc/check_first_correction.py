"""Check the first two asymptotic coefficients by exact finite differences."""
from fractions import Fraction as F
from math import factorial, comb
from check import egf_coefficient


def forward_difference(values):
    return [b-a for a,b in zip(values,values[1:])]


def inverse_fact(m):
    return F(1,factorial(m)) if m >= 0 else F(0)


def run():
    checked=0
    for j in (2,3,4,5):
        b=F(j+2,j+1)
        v2=1+(F(1,2) if j>2 else 0)
        c=v2+F(1,j+1)+F(1,(j+1)*(j+2))
        for r in range(j):
            for h in (0,1,2):
                m=r+j*h
                values=[egf_coefficient(j,d,r,h)/b**m for d in range(h,h+m+2)]
                if m==0:
                    assert set(values)=={1}
                else:
                    diff=values
                    for _ in range(m-1):
                        diff=forward_difference(diff)
                    last=forward_difference(diff)
                    assert set(last)=={1}
                    # For d=h+x, extract [d^(m-1)] from the Newton coefficients.
                    observed=diff[0]*inverse_fact(m-1) - (m*h+comb(m,2))*inverse_fact(m)
                    predicted=-(m*h+comb(m,2))*inverse_fact(m)+inverse_fact(m-1)/b+c/b**2*inverse_fact(m-2)
                    assert observed==predicted,(j,r,h,observed,predicted)
                checked+=1
    print(f'{checked} exact residue/offset cases passed, including the constant term.')


if __name__=='__main__':
    run()
