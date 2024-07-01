import sympy
from sympy.abc import x
from functools import reduce
from sympy import mod_inverse
from sympy import *
x = sympy.Symbol('x')
import numpy as np
class Decoding_GRS():
    def __init__(self, alphas, betas, message, e, Mod):
        self.alphas, self.betas, self.message, self.e, self.Mod = alphas, betas, message, e, Mod
        self.n, self.k = len(self.alphas), len(self.message)
    def encoding(self):
        self.G = np.zeros((self.k,self.n), dtype = int)
        for i in range(self.k):
            for j in range(self.n):
                self.G[i, j] = np.mod((self.betas[j]*(self.alphas[j])**i),self.Mod)
        codeword = np.mod( np.dot( self.message,self.G ) , self.Mod)
        self.ciphertext = list()
        for i in range(self.n ):
            aux = np.mod( ( codeword[i] + self.e[i]  ) ,  self.Mod)
            self.ciphertext.append(aux)
    def Lagrange(self,x):
        prod = lambda lst: reduce(lambda x, y: x * y, lst, 1)
        return sum([ prod([(x - self.alphas[j]) % self.Mod for j in range(self.n ) if j != i]) % self.Mod for i in range( self.n )]) % self.Mod
    def compute_syndrome(self):
        self.List, self.S  = list(),list()
        for i in self.alphas:
            aux = self.Lagrange(i)
            self.List.append(aux)
        self.beta_prime = [(mod_inverse(self.betas[i] * self.List[i], self.Mod ) ) for i in range( self.n )]
        dim = len(self.ciphertext) - len(self.message)
        for l in range(dim):
            aux = 0
            for j in range(self.n  ):
                aux += (self.ciphertext[j] * self.beta_prime[j] * (self.alphas[j] ** l)) 
            aux = aux % self.Mod
            self.S.append(aux)
        return self.S    
    def Syndrome_polynomial_Sx(self):
        S_l = ""
        for l in range(len(self.compute_syndrome() )):
            if l == 0: S_l += f"{self.compute_syndrome()[l]}"
            else: S_l += f" + {self.compute_syndrome()[l]}*x^{l}"
        return S_l
    def Division(self,pol1, pol2):
        A = sympy.Poly(pol1,  modulus = self.Mod)
        B = sympy.Poly(pol2 , modulus = self.Mod)
        quotient, remainder = sympy.div(A, B)
        adjust_to_gf13  = lambda coef: coef % Mod
        quotient_coefs  = [adjust_to_gf13(c) for c in quotient.all_coeffs()]
        remainder_coefs = [adjust_to_gf13(c) for c in remainder.all_coeffs()]
        quotient_poly   = sympy.Poly(quotient_coefs, x)
        remainder_poly  = sympy.Poly(remainder_coefs, x)
        quotients.append( quotient )
        rest.append( remainder_poly.as_expr() )
        return  rest, quotients
    def compute_roots(self):
        for i in range(3):
            self.Division(rest[i], rest[-1])
        t_menos_1  = 0
        t_0        = 1
        t1         =  (t_menos_1 -  (5*x)*(t_0) ) % self.Mod
        t2         = (1 -  (8*x*12*x % self.Mod +8*x*6%13 ))% self.Mod
        self.t2 = t2.args[0]  
    def equation(self):
        expr = self.t2
        a = expr.coeff(x, 2) % self.Mod
        b = expr.coeff(x, 1) % self.Mod
        c = expr.coeff(x, 0) % self.Mod
        J = list()
        discriminant = (b**2 - 4*a*c) % self.Mod
        squares = [i**2 % self.Mod for i in range(self.Mod)]
        if discriminant in squares:
            sqrt_discriminant = squares.index(discriminant )
            _2_a = (2*a) % self.Mod
            modular_inverse = mod_inverse(_2_a, self.Mod)
            root1 = ((-b + sqrt_discriminant ) * modular_inverse) % self.Mod
            inverse_root1 = (1*sympy.mod_inverse(root1, self.Mod))%self.Mod
            root2 = ((-b - sqrt_discriminant) * modular_inverse) % self.Mod
            inverse_root2 = (1*sympy.mod_inverse(root2, self.Mod))%self.Mod
            self.error_position =  sorted([alphas.index(i) for i in [inverse_root1 , inverse_root2]  ])
            return self.error_position
        else:
            print("No real solutions in mod 13", discriminant)
    def find_error(self):
        i, j = self.equation()
        e = list(np.zeros(self.n, dtype = int))
        alpha3, alpha9 = self.alphas[i], self.alphas[j]
        beta3, beta9 = self.beta_prime[i], self.beta_prime[j]
        e_3, e_9 = (-alpha3*8*sympy.mod_inverse(beta3*7,self.Mod) )% self.Mod, (-8*beta9*sympy.mod_inverse(72, self.Mod) )% self.Mod
        for idx , value in zip(self.error_position, [e_3, e_9]):
            e[idx] = value
        self.codeword_recover = [(self.ciphertext[i] - self.e[i] )% self.Mod for i in range(self.n )]
        return self.codeword_recover
    def recover_message(self):
        matrix_prod                  = np.mod(np.dot(self.G,np.transpose(self.G)),self.Mod)
        matrix_inverse               = np.array(sympy.Matrix(matrix_prod).inv_mod(self.Mod)).astype(int)
        codeword_matrixTransp        = np.mod(np.dot(self.codeword_recover,np.transpose(self.G)),Mod)
        matrixG_matrixTranspG_inversa= np.mod(np.dot(codeword_matrixTransp,matrix_inverse),self.Mod)
        print("Donne! ")
        return np.transpose( matrixG_matrixTranspG_inversa)
    def run(self):
        self.encoding()
        self.compute_syndrome()
        self.Syndrome_polynomial_Sx()
        self.compute_roots()
        self.find_error()
        print("recovered message: ",self.recover_message() )
alphas, betas    = [2,4,1,5,3,7,6,9,8], [2,5,1,7,2,5,1,2,3]
message, e       = [5,1,4,2,3],[0,0,5,0,0,0,0,0,3]
r_1, r_0         = x**4, 8*x**3 + 12*x + 7 
rest,quotients,t = [x**4, 8*x**3 + 12*x + 7], [],[0,1]
Mod = 13
decode = Decoding_GRS(alphas, betas, message,e,  Mod)
decode.run()
