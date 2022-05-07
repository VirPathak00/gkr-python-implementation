#sum check protocol 
#(to make this a valid noninteractive version of sumcheck, need to use a hash function instead of the random library)
import random
from random import randint

# I ended up just using a fixed prime instead of generating a new one every time. So one needs to change that prime
#value based on the level of security desired. Just change the p variable to a new prime. 
first_primes_list = [
    2,
    3,
    5,
    7,
    11,
    13,
    17,
    19,
    23,
    29,
    31,
    37,
    41,
    43,
    47,
    53,
    59,
    61,
    67,
    71,
    73,
    79,
    83,
    89,
    97,
    101,
    103,
    107,
    109,
    113,
    127,
    131,
    137,
    139,
    149,
    151,
    157,
    163,
    167,
    173,
    179,
    181,
    191,
    193,
    197,
    199,
    211,
    223,
    227,
    229,
    233,
    239,
    241,
    251,
    257,
    263,
    269,
    271,
    277,
    281,
    283,
    293,
    307,
    311,
    313,
    317,
    331,
    337,
    347,
    349,
]

p = 7793

def nBitRandom(n):
    return random.randrange(2 ** (n - 1) + 1, 2**n - 1)


def getLowLevelPrime(n):
    """Generate a prime candidate divisible
    by first primes"""
    while True:
        # Obtain a random number
        pc = nBitRandom(n)

        # Test divisibility by pre-generated
        # primes
        for divisor in first_primes_list:
            if pc % divisor == 0 and divisor**2 <= pc:
                break
        else:
            return pc


def isMillerRabinPassed(mrc):
    """Run 20 iterations of Rabin Miller Primality test"""
    maxDivisionsByTwo = 0
    ec = mrc - 1
    while ec % 2 == 0:
        ec >>= 1
        maxDivisionsByTwo += 1
    assert 2**maxDivisionsByTwo * ec == mrc - 1

    def trialComposite(round_tester):
        if pow(round_tester, ec, mrc) == 1:
            return False
        for i in range(maxDivisionsByTwo):
            if pow(round_tester, 2**i * ec, mrc) == mrc - 1:
                return False
        return True

    # Set number of trials here
    numberOfRabinTrials = 20
    for i in range(numberOfRabinTrials):
        round_tester = random.randrange(2, mrc)
        if trialComposite(round_tester):
            return False
    return True


if __name__ == "__main__":
    while True:
        n = 1024
        prime_candidate = getLowLevelPrime(n)
        if not isMillerRabinPassed(prime_candidate):
            continue
        else:
            p = prime_candidate
            break



#Sumcheck needs us to generate bitstrings of length n if our function is takes in length-n tuples.
def generate_binary_strings(bit_count):
    binary_strings = []

    def genbin(n, bs=""):
        if len(bs) == n:
            binary_strings.append(bs)
        else:
            genbin(n, bs + "0")
            genbin(n, bs + "1")

    genbin(bit_count)
    return binary_strings


def Convert(string):
    list1 = []
    list1[:0] = string
    return list1


def sumcheck(value, poly, variable_length):

    if(variable_length == 1 and (poly([0]) + poly([1]) % p) == value % p):
        return True
    
    global g_vector 
    global r 

    g_vector = [0] * (variable_length)
    r = [0] * (variable_length)

    def g_1(x_1):
        ell = generate_binary_strings(variable_length - 1)
        for i in range(len(ell)):
            ell[i] = Convert(ell[i])
            for j in range(len(ell[i])):
                ell[i][j] = int(ell[i][j])

        for i in range(len(ell)):
            ell[i].insert(0, x_1)

        output = 0

        for i in range(2 ** (variable_length - 1)):
            output += poly(ell[i])
        return output % p

    if (g_1(0) + g_1(1)) % p != value: #first sumcheck check
        return False
    else:
        r[0] = randint(0, p - 1)
        g_vector[0] = g_1(r[0]) % p

    for j in range(1, variable_length - 1): #repeats the steps described above


        def g(x):
            ell = generate_binary_strings(variable_length - j - 1)
            for i in range(len(ell)):
                ell[i] = Convert(ell[i])
                for k in range(len(ell[i])):
                    ell[i][k] = int(ell[i][k])

            for i in range(len(ell)):
                ell[i] = r[0 : j] + [x] + ell[i]

            output = 0
            for i in range(len(ell)):
                output += poly(ell[i]) 
            return output % p

        if g_vector[j - 1] != (g(0) + g(1)) % p:
            return False
        else:
            r[j] = randint(0, p - 1)
            g_vector[j] = g(r[j]) % p

    def g_v(x_v):
        eval_vector = r
        eval_vector[variable_length - 1] = x_v
        return poly(eval_vector)

    if (g_v(0) + g_v(1)) % p != g_vector[variable_length - 2]:
        return False
    else:
        r[variable_length - 1] = randint(0, p - 1)
        g_vector[variable_length - 1] = g_v(r[variable_length - 1]) % p
        return True

def get_r():
    return r

#this check isn't actually needed in the gkr protocol, so we don't include it in the sum-check function
#but we add it for completeness.
def lastcheck(poly, x, variable_length, value):
  if (poly(x) % p != g_vector[variable_length - 1] % p) or sumcheck(value, poly, variable_length) == False: 
    return False
  return True

