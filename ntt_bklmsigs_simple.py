from copy import deepcopy
from hashlib import shake_256
from math import ceil, log2, sqrt
from secrets import randbelow, randbits
from sympy.utilities.iterables import ibin
from numpy import matmul, array, sqrt, transpose, longlong,polymul,add, vander



KEY_GEN_SALT = b'KEY GENERATION SALT'  # These salts MUST be included and MUST be all different.
SIG_CH_SALT = b'SIGNATURE CHALLENGE SALT'  # Can change these salts to '00', '01', and '10' and maintain security...
SIG_AG_SALT = b'SIGNATURE AGGREGATION SALT'  # Important part is only that they are included and different


#here I import functions for use in the ntt poly mul function
def transform_radix_2(vector, root, mod):
    n = len(vector)

    levels = n.bit_length() - 1
    if 1 << levels != n:
        raise ValueError("Length is not a power of 2")

    def reverse(x, bits):
        y = 0
        for i in range(bits):
            y = (y << 1) | (x & 1)
            x >>= 1
        return y

    for i in range(n):
        j = reverse(i, levels)
        if j > i:
            vector[i], vector[j] = vector[j], vector[i]
    powtable = []
    temp = 1
    for i in range(n // 2):
        powtable.append(temp)
        temp = temp * root % mod

    size = 2
    while size <= n:
        halfsize = size // 2
        tablestep = n // size
        for i in range(0, n, size):
            k = 0
            for j in range(i, i + halfsize):
                l = j + halfsize
                left = vector[j]
                right = vector[l] * powtable[k]
                vector[j] = (left + right) % mod
                vector[l] = (left - right) % mod
                k += tablestep
        size *= 2
    return vector

def intt(seq, par, inverse=True):
    prime = par['modulus']

    #this step changes modulus to an int, somewhat superfluous
    p = prime

    a = [i for i in seq]

    n = len(a)
    if n < 1:
        return a

    b = n.bit_length() - 1
    if n & (n - 1):
        b += 1
        n = 2 ** b

    if (p - 1) % n:
        raise ValueError("Expected prime modulus of the form (m*2**k + 1)")

    a += [0] * (n - len(a))

    for i in range(1, n):
        j = int(ibin(i, b, str=True)[::-1], 2)
        if i < j:
            a[i], a[j] = a[j], a[i]

    pr = par['root']

    rt = pow(pr, (p - 1) // n, p)
    if inverse:
        rt = pow(rt, p - 2, p)

    w = [1] * (n // 2)
    for i in range(1, n // 2):
        w[i] = w[i - 1] * rt % p

    h = 2
    while h <= n:
        hf, ut = h // 2, n // h
        for i in range(0, n, h):
            for j in range(hf):
                u, v = a[i + j], a[i + j + hf] * w[ut * j]
                a[i + j], a[i + j + hf] = (u + v) % p, (u - v) % p
        h *= 2

    if inverse:
        rv = pow(n, p - 2, p)

        a = [x * rv % p for x in a]

    return a


def get_prime(par):
    """ Input parameter dictionary with pos integer 'minbits,' output smallest prime with at least this many bits. """
    bits_in_prime = par['minbits']
    assert isinstance(bits_in_prime, int)
    assert bits_in_prime >= 1
    x = 2 ** (bits_in_prime - 1) + 1
    while any(x % y == 0 for y in range(2, ceil(sqrt(x)))):
        x += 1
    return x


def get_prime_with_root_of_unity(par):
    """ Input parameter dictionary with pos integers 'minbits' and 'unity,' output smallest prime with at least
    'minbits' bits and such that Z/qZ has a 'unity'-th primitive root of unity.
    """
    bits_in_prime = par['minbits']
    desired_root_of_unity = par['unity']

    x = 2 ** (bits_in_prime - 1) + 1
    ct = 0
    found = (x - 1) % desired_root_of_unity == 0
    found = found and not any(x % _ == 0 for _ in range(2, ceil(sqrt(x)) + 1))
    while not found:
        # if ct % 2 ** 16 == 0:
        #     print(str(x) + " has " + str(log2(x)) + " bits and is not the number we are looking for.")
        x += desired_root_of_unity
        ct += 1
        found = (x - 1) % desired_root_of_unity == 0
        found = found and all(x % _ != 0 for _ in range(2, ceil(sqrt(x)) + 1))
    return x


def setup(par):
    """ Outputs setup parameters.
    All the setup parameters decided upon in here MUST be checked.
    The parameter par['sec'] = sec_level = log2(number of bits of desired security).
        - For example, for 128 = 2**7 bits of security, use sec_level = 7, for 256 = 2**8 bits of security, use
          sec_level = 8, and etc.
        - Sample 2**sec_level-bit secret seeds uniformly (up to negl. bias) from 0, 1, ..., 2**(2**sec_level) - 1
        - Compute N-bit numbers uniformly (up to negl. bias) modulo q by evaluating secure extendable output functions
          like SHAKE256 to output N+2**sec_level-bit integers from 0 , 1, ..., 2**(N+2**sec_level) - 1 and modding by q.
        - The parameters for the scheme (d, q, l) are independent of the security parameter; they are set at values
          we think exceed 128 bits of post-quantum security, but these values must be checked.
          Parameters here come from the BK paper and should be considered insecure choices (see warning at top of doc!)
          Output variable parameters depending on desired security level. Presently, this method only outputs fixed
          parameters we suspect are 128-bit secure against quantum computers. In this sample code, the security
          parameter is only used for sampling numbers without bias from Z/qZ.
    """
    assert 'agg cap' in par
    agg_cap = par['agg cap']
    assert isinstance(agg_cap, int)
    assert agg_cap >= 1
    assert 'sec' in par
    sec_level = par['sec']
    assert sec_level >= 2

    d = 1024  # Common choice of d for high levels of PQ security
    q = 2147493889  # Smallest prime with >= 32 bits and a 2d-th root of unity to agg 32 sigs. Use 40 bits 1024 sigs
    w = 2991620  # 2d-th root of unity - see later, only used in NTT implementation of polynomial mult (incoming/to do)
    l: int = 2 * ceil(log2(q))  # THIS NEEDS TO BE CHECKED
    par['root'] = w
    par['modulus'] = q
    par['length'] = l
    par['degree'] = d
    par['sk bound'] = 1
    par['ch bound'] = 1
    par['ag bound'] = 1
    par['otesk bound'] = 1

    # This choice of bound_vf is tightest possible so semi-honest signatures correctly pass verification
    # A thorough analysis of the security parameters is strongly recommended
    par['vf bound'] = agg_cap * d * par['ag bound'] * par['sk bound'] * (1 + d * par['ch bound'])
    assert 2 * par['vf bound'] + 1 < q

    a = []
    while len(a) < l:
        a += [[]]
        while len(a[-1]) < d:
            a[-1] += [randbelow(q) - (q - 1) // 2]
    par['rsis ch'] = a

    num_polys_needed_for_esk = 2 * par['length']
    num_coefs_per_poly = par['degree']
    bits_per_coef = ceil(log2(2 * par['sk bound'] + 1))
    bytes_per_coef = ceil(bits_per_coef / 8.0)
    assert bytes_per_coef >= 1
    bytes_to_roll_coef = 2 ** (par['sec'] - 3) + bytes_per_coef  # bytes so div-by-8
    bytes_to_roll_poly = num_coefs_per_poly * bytes_to_roll_coef
    bytes_to_roll_esk = num_polys_needed_for_esk * bytes_to_roll_poly

    par['bits to roll esk coef'] = 8 * bytes_to_roll_coef
    par['bits to roll esk poly'] = 8 * bytes_to_roll_poly
    par['bits to roll esk'] = 8 * bytes_to_roll_esk

    #new shit
    num_polys_needed_for_otesk = 2 * par['length']
    num_coefs_per_poly = par['degree']
    bits_per_coef = ceil(log2(2 * par['otesk bound'] + 1))
    bytes_per_coef = ceil(bits_per_coef / 8.0)
    # assert bytes_per_coef >= 1
    bytes_to_roll_coef = 2 ** (par['sec'] - 3) + bytes_per_coef  # bytes so div-by-8
    bytes_to_roll_poly = num_coefs_per_poly * bytes_to_roll_coef
    bytes_to_roll_otesk = num_polys_needed_for_otesk * bytes_to_roll_poly

    par['bits to roll otesk coef'] = 8 * bytes_to_roll_coef
    par['bits to roll otesk poly'] = 8 * bytes_to_roll_poly
    par['bits to roll otesk'] = 8 * bytes_to_roll_otesk
    #end new shit


    return par



def bin_dig_to_esk(par, bdig):
    assert len(bdig) == par['bits to roll esk']
    assert par['bits to roll esk'] % par['bits to roll esk poly'] == 0
    esk = []
    i = 0
    while len(esk) < 2:
        esk += [[]]
        while len(esk[-1]) < par['length']:
            next_piece = bdig[i * par['bits to roll esk poly']: (i + 1) * par['bits to roll esk poly']]
            lnp = len(next_piece)
            assert lnp >= par['bits to roll esk poly']
            tmp = bin_dig_to_poly(par, next_piece, par['sk bound'])
            esk[-1] += [tmp]
            i += 1
    return esk


def sk_msg(par, sk):
    if isinstance(sk, str):
        sk_as_str = sk
    else:
        sk_as_str = str(sk)
    return (KEY_GEN_SALT.decode() + "," + sk_as_str).encode()


def sk_to_esk(par, sk):
    # outbytes = 2 * par['length'] * par['degree'] * (2 ** par['sec'] + ceil(log2(2 * par['sk bound'] + 1))) // 8
    assert par['sec'] >= 3
    outbytes = par['bits to roll esk'] // 8
    tmp = sk_msg(par, sk)
    tmp = bin_dig(par, tmp, outbytes)
    return bin_dig_to_esk(par, tmp)


def central(par, x, bd=None):
    """ Can be made constant time and very fast by bit-shifting x to obtain the sign and using logical ops. See
    CRYSTALS-DILITHIUM round 3 submission for more details to do this in constant time."""
    #assert isinstance(x, int)
    #assert 'modulus' in par
    #assert bd is None or (isinstance(bd, int) and 0 <= bd <= (par['modulus'] - 1) // 2)
    if bd is None:
        bd = (par['modulus'] - 1) // 2
    x = x % (2 * bd + 1)
    if x > bd:
        x -= (2 * bd + 1)
    return x



def poly_add(par, f, g):
    tmp = [(x + y) % par['modulus'] for x, y in zip(f, g)]
    return [central(par, _) for _ in tmp]


def rot(x):
    y = deepcopy(x)
    tmp = [deepcopy(y)]
    last = y[-1]
    first = y[:-1]
    while len(tmp) < len(y):
        tmp += [[-1 * last] + first]
        last = tmp[-1][-1]
        first = tmp[-1][:-1]
    tmp = transpose(array(tmp, longlong)).tolist()
    return tmp

def poly_mul(par, f, g):
    """ Multiply two polynomials. """
    a = rot(f)
    a = array(a, longlong)
    b = array(g, longlong)
    tmp = matmul(a, b)
    tmp = tmp.tolist()
    tmp = [central(par, _) for _ in tmp]
    return tmp

'''
#new, faster ntt poly mul function
def ntt_poly_mul(par, f, g):
    a, b = f[:], g[:]
    q = par['modulus']
    w = par['root']
    n = m = len(a) + len(b)

    if n > 0 and n & (n - 1):  # not a power of 2
        n = 2 ** n.bit_length()

    a += [0]*(n-len(a))
    b += [0]*(n-len(b))

    a = array(a,longlong)
    b = array(b,longlong)


    radix1 = transform_radix_2(a,w,q)
    radix2 = transform_radix_2(b,w,q)
    ccz = array(radix1, longlong)
    czz = array(radix2, longlong)
    cz = [x*y for x,y in zip(ccz,czz)]
    #cz = array([central(par,x*y) for x,y in zip(ccz,czz)],longlong)
    invert = array(intt(cz, par,inverse=True),longlong)
    length = len(invert)
    half = length // 2
    space = half + 5

    for i in range(len(invert)):
        tmp = invert[i]

        if i % 2 == 0:
            new = (i * space) % length
            cz[new] = tmp
        else:
            new = ((i * space) + half) % length
            cz[new] = tmp

    result = cz

    return result
'''
#new, faster ntt poly mul function
def ntt_poly_mul(par, f, g):
    a, b = f[:], g[:]
    q = par['modulus']
    w = par['root']
    n = m = len(a) + len(b)

    if n > 0 and n & (n - 1):  # not a power of 2
        n = 2 ** n.bit_length()

    a += [0]*(n-len(a))
    b += [0]*(n-len(b))


    radix1 = transform_radix_2(a,w,q)
    radix2 = transform_radix_2(b,w,q)


    ccz = radix1
    czz = radix2
    cz = [(x*y) for x,y in zip(ccz,czz)]
    print('F(f).F(g): '+ str(sum(cz)))
    invert = intt(cz,par,inverse=True)

    return result


def poly_lin_combo(par, polys, coefs):
    assert isinstance(polys, list)
    for poly in polys:
        assert isinstance(poly, list)
        assert len(poly) == par['degree']
    for coef in coefs:
        assert isinstance(coef, list)
        assert len(coef) == par['degree']
    tmp = [0] * par['degree']
    for poly, coef in zip(polys, coefs):
        tmp_tmp = poly_mul(par, poly, coef)
        tmp = poly_add(par, tmp, tmp_tmp)
    return [central(par, _) for _ in tmp]


def esk_to_vk(par, esk):
    """ Input a parameter dictionary par and an expanded secret key esk, output the verification key vk"""
    q = par['modulus']
    d = par['degree']
    a = par['rsis ch']
    vk = []
    nonce = 0
    while len(vk) < 2:
        # print('.', end='')
        # print"Computing matrix-of-polynomials multiplication")
        tmp = poly_lin_combo(par, esk[nonce], a)
        assert isinstance(tmp, list)
        assert len(tmp) == d
        vk += [tmp]
        nonce += 1
    # return [poly_lin_combo(par, esk[0], par['rsis ch']), poly_lin_combo(par, esk[0], par['rsis ch'])]
    return vk


def keygen(par):
    """ Generate small secret seed sk, expand to an expanded secret key esk, evaluate to public verf key vk, then
    output sk, esk, vk.
    """
    sec_level = par['sec']
    bits_per_secret_seed = 2 ** sec_level
    sk_as_int = randbits(bits_per_secret_seed)  # Do not broadcast random tape of your machine! Keep secret.
    sk_as_binary = bin(sk_as_int)[2:].zfill(bits_per_secret_seed)
    esk = sk_to_esk(par, sk_as_binary)
    assert esk == [[[central(par, _) for _ in row] for row in each_esk] for each_esk in esk]
    vk = esk_to_vk(par, esk)
    return sk_as_binary, esk, vk


def bin_dig(par, encoded_msg, outbytes):
    s = shake_256()
    s.update(encoded_msg)
    # print("Extracting " + str(outbytes) + " bytes")
    hexdigest = s.hexdigest(outbytes)
    # print("Done, casting as binary.")
    intdigest = int(hexdigest, 16)
    bindigest = bin(intdigest)[2:].zfill(8 * outbytes)
    assert len(bindigest) == 8 * outbytes
    return bindigest

'''
def bin_dig_to_poly(par, bdig, bound):
    assert len(bdig) >= par['bits to roll esk poly']
    result = []
    i = 0
    assert isinstance(bdig, str)
    while len(result) < par['degree']:
        sect = bdig[i * par['bits to roll esk coef']: (i + 1) * par['bits to roll esk coef']]
        tmp = int(sect, 2)
        tmp = tmp % (2 * bound + 1)
        tmp = tmp - bound
        result += [tmp]
        i += 1
    assert all(central(par, _) == _ for _ in result)
    return result
'''
def bin_dig_to_poly(par, bdig, bd):
    """ Take as input a binary digest and a bound, partition the digest into sub-strings, interpret each sub-string as
    an integer modulo the bound, and interpret the resulting sequence of integers as the coefficients of a polynomial.
    """
    #assert len(bdig) >= par['bits to roll otesk poly']
    #assert len(bdig) % par['bits to roll otesk coef'] == 0  # Ensures input bits can be partitioned into blocks.
    poly = []
    i = 0
    # assert isinstance(bdig, str)
    while len(poly) < 2*par['degree']:
        #sect = bdig[i * par['bits to roll otesk coef']: (i + 1) * par['bits to roll otesk coef']]
        sect = bdig[i]
        tmp = int(sect, 2)
        tmp = tmp % (2 * bd + 1)
        tmp = central(par, tmp, bd)
        poly += [tmp]
        i += 1
    # assert all(_central(par, _) == _ for _ in poly)
    return poly


def sig_chall_msg(vk, m):
    assert isinstance(m, str)
    return (SIG_CH_SALT.decode() + "," + str(vk[0]) + "," + str(vk[1]) + "," + m).encode()


def hash_to_sig_chall(par, vk, m):
    one_poly = [0] * par['degree']
    one_poly[0] = 1
    bdig = bin_dig(par, sig_chall_msg(vk, m), par['bits to roll esk poly'] // 8)
    ch = bin_dig_to_poly(par, bdig, par['ch bound'])
    return [one_poly, ch]


def vect_scale(par, x, c):
    assert isinstance(x, list)
    assert isinstance(c, list)
    assert len(x) == par['length']
    assert len(c) == par['degree']
    assert all(len(_) == par['degree'] for _ in x)
    result = []
    for _ in x:
        result += [poly_mul(par, _, c)]
    return result


def vect_add(par, x, y):
    return [poly_add(par, xx, yy) for xx, yy in zip(x, y)]


def vect_lin_combo(par, vects, coefs):
    assert isinstance(coefs, list)
    assert isinstance(vects, list)
    assert len(coefs) == len(vects)
    '''for vect, coef in zip(vects, coefs):
        assert isinstance(vect, list)
        assert len(vect) == par['length']
        assert isinstance(coef, list)
        assert len(coef) == par['degree']
        for x in vect:
            assert isinstance(x, list)
            assert len(x) == par['degree'] '''
    zero_poly = [0] * par['degree']
    tmp = [deepcopy(zero_poly)] * par['length']
    for vect, coef in zip(vects, coefs):
        tmp_tmp = vect_scale(par, vect, coef)
        tmp = vect_add(par, tmp, tmp_tmp)
    return [[central(par, _) for _ in row] for row in tmp]  # 303 in the hizzy


def sign(par, esk, vk, m):
    tmp = hash_to_sig_chall(par, vk, m)
    tmp = vect_lin_combo(par, esk, tmp)
    return tmp


def agg_hash_len_dig(par, vks):
    assert isinstance(vks, list)
    assert len(vks) <= par['agg cap']
    return len(vks) * par['bits to roll esk poly']  # bits to roll esk poly = bits to roll any poly


def agg_hash_msg(par, vks):
    return (SIG_AG_SALT.decode() + "," + str(vks)).encode()


def bin_dig_to_agg_coefs(par, vks, bdig):
    x = len(bdig)
    y = len(vks)
    assert x % y == 0
    r = x // y
    assert isinstance(r, int)
    assert r >= par['bits to roll esk poly']
    tmp = []
    for i in range(len(vks)):
        tmp += [bin_dig_to_poly(par, bdig[i * r: (i + 1) * r], par['ag bound'])]
    return tmp


def hash_to_agg_coefs(par, vks):
    """ Assumes vks is sorted """
    return bin_dig_to_agg_coefs(par, vks, bin_dig(par, agg_hash_msg(par, vks), agg_hash_len_dig(par, vks)))


def aggregate(par, vks, sigs):
    assert isinstance(sigs, list)
    assert isinstance(vks, list)
    assert len(sigs) == len(vks)
    for sig in sigs:
        assert isinstance(sig, list)
        assert len(sig) == par['length']
        for _ in sig:
            assert isinstance(_, list)
            assert len(_) == par['degree']
    for vk in vks:
        assert isinstance(vk, list)
        assert len(vk) == 2
        for _ in vk:
            assert len(_) == par['degree']
    tmp = hash_to_agg_coefs(par, vks)
    tmp = vect_lin_combo(par, sigs, tmp)
    return tmp


def sig_targ(par, vk, m):
    return poly_lin_combo(par, vk, hash_to_sig_chall(par, vk, m))  # polynomials


def sig_targs(par, vks, ms):
    return [sig_targ(par, vk, m) for vk, m in zip(vks, ms)]


def agg_sig_targs(par, vks, ms):
    return poly_lin_combo(par, sig_targs(par, sorted(vks), ms), hash_to_agg_coefs(par, sorted(vks)))  # polynomials


def negate(f):
    return [-_ for _ in f]


def eval_sig(par, sig):
    return poly_lin_combo(par, sig, par['rsis ch'])  # polynomials


def correct(par, signature, vks, ms):
    tmp = agg_sig_targs(par, vks, ms)
    tmp = negate(tmp)
    tmp = poly_add(par, eval_sig(par, signature), tmp)  # recall poly_add centralizes
    return all(not _ for _ in tmp)


def bnd_chk(par, x):
    y = deepcopy(x)
    while isinstance(y[0], list):
        y = [_ for z in y for _ in z]
    return all(abs(_) <= par['vf bound'] for _ in y)


def verify(par, sig, vks, ms):
    b1 = bnd_chk(par, sig)
    b2 = correct(par, sig, vks, ms)
    return b1, b2


#polymulmod function for checking values of multiplying polynomials
def polymulmod(A, B, m, n,par):

    q = par['modulus']
    prod = [0] * (m + n -1)
    a = array(A,longlong)
    b = array(B,longlong)

    # Multiply two polynomials term by term

    # Take every term of first polynomial
    for i in range(m):

        # Multiply the current term of first
        # polynomial with every term of
        # second polynomial.
        for j in range(n):

            prod[i + j] += a[i]*b[j]
    output = array([i for i in prod],longlong)

    return output


par = setup({'agg cap': 32, 'sec': 7})
filekey = open("sample_key.dat","r")
store = filekey.read()
filekey.close()
keys = eval(store)
f = par['rsis ch'][0]
g = par['rsis ch'][1]
vanf = vander(array(f,longlong))
vang = vander(array(g,longlong))
print(vanf)
print(vang)
print(sum(vanf)==sum(vang))

oldpoly = polymulmod(f,g,len(f),len(g),par)
pol = poly_mul(par,f,g)
nut = ntt_poly_mul(par,f,g)

nppol = polymul(f,g)

npmod = [i%par['modulus'] for i in nppol]

h1 = npmod[0:(len(npmod)//2)+1]
h2 = npmod[(len(npmod)//2):len(npmod)]
h2.append(0)

h12 = [(x-y) for x,y in zip(h1,h2)]
fin = [central(par, _) for _ in h12]
