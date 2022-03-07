#import libraries
import hashlib
import secrets
import random
import numpy as np
import math
import os
from sympy import ntt, intt
from NTT import transform,inverse_transform, find_params_and_transform,is_prime
from NTT_new import NTT

Zq = 2147484161
w = 14842998

#write a function for computing two polynomials using NTT
def ntt_poly_mul(a,b,root,q):
    #check if q is prime
    if is_prime(q) == True:
        a,b = a[:],b[:]
        n = m = len(a) + len(b) - 1

        if n > 0 and n&(n - 1): # not a power of 2
            n = 2**n.bit_length()
        
        a += [0]*(n-len(a))
        b += [0]*(n-len(b))

        a,b = transform(a,root,q),transform(b,root,q)
        a = [x*y%q for x,y in zip(a,b)]
        a = inverse_transform(a,root,q)[:m]

        return a

    else:
        return 'q must be a prime modulus greater than M'

def new_ntt_poly_mul(a,b,root,q):
    #check if q is prime
    new_ntt = NTT()
    if is_prime(q) == True:
        a,b = a[:],b[:]
        n = m = len(a) + len(b) - 1

        if n > 0 and n&(n - 1): # not a power of 2
            n = 2**n.bit_length()

        a += [0]*(n-len(a))
        b += [0]*(n-len(b))
        length = len(a)

        a,b = new_ntt.ntt(a,q,length,root),new_ntt.ntt(b,q,length,root)
        a = [x*y%q for x,y in zip(a,b)]
        a = new_ntt.intt(a,q,length,root)[:m]

        return a

    else:
        return 'q must be a prime modulus greater than M'


def polymulmod(A, B, m, n,q):

    prod = [0] * (m + n)

    # Multiply two polynomials term by term 

    # Take every term of first polynomial 
    for i in range(m):

        # Multiply the current term of first  
        # polynomial with every term of  
        # second polynomial. 
        for j in range(n):

            prod[i + j] += A[i]*B[j]
    output = [i%q for i in prod]
    return output



'''
#print(polymulmod(test1,test2,len(test1),len(test2),769))
print(ntt_poly_mul(test1,test2,40,769))
print(find_params_and_transform([3,2,1,0,0,0,0,0],769))
print(find_params_and_transform([5,0,2,0,0,0,0,0],769))
print('_____________________________________________')
'''
