# import bib

import numpy as np
from itertools import combinations
from sympy import Matrix, mod_inverse
import random, time, os, glob, pandas
import matplotlib.pyplot as plt
from memory_profiler import memory_usage
from datetime import datetime
class ENCRYPT():
    def __init__(self):
        np.random.seed(2024)
        self.execution_times_McEliece, self.memory_McElice = 0, 0
        self.execution_times_Lee_Brickell, self.memory_Lee_Brickell = 0,0
        self.execution_times_Leon, self.memory_Leon = 0, 0
        self.diretorio_script = os.path.dirname(os.path.abspath(__file__))
        self.folder_path = os.path.join(self.diretorio_script, f'results {datetime.now().strftime("%Y-%m-%d")}')
        self.Generator_matrix , self.Parity_matrix = dict(),dict()
        self.modulus = 2
        self.l = 3
        self.p = 3
        self.result = list() 
    def read_text_files(self):
        if not os.path.exists(self.folder_path):
            os.makedirs(self.folder_path)
        # Get a list of all text files in the specified folder
        self.text_files = glob.glob(os.path.join(self.folder_path, "*.txt"))
        matrix = []
        for file_path in self.text_files:
            file_name = os.path.basename(file_path)
            try:
                with open(file_path, 'r') as file:
                    self.n = int(file.readline().strip())  # Read the number of k
                    self.k = int(file.readline().strip())  # Read the number of n
                    self.t = int(file.readline().strip())  # Read the number of t
        
                    if file_name                             == f"Parity Matrix {int(self.n - self.k)}_{self.n}.txt":
                        parity_matrix = list()
                        for line in file:
                            rows =  list(map(int, line.strip().split())) 
                            parity_matrix.append(rows)
                        self.Parity_matrix[(self.k, self.n)] =  parity_matrix      
                    elif file_name   == f"Generator Matrix {int(self.k)}_{self.n}.txt":
                        generator_matrix = list()
                        for line in file:
                            rows = list (  map( int , line.strip().split()))
                            generator_matrix.append(rows)
                        self.Generator_matrix[(self.k, self.n)] = generator_matrix   
                    else:
                        continue
                       
            except Exception as e:
                print(f"An error occurred while reading {file_path}: {e}")
        
        return self.Generator_matrix, self.Parity_matrix 
    def is_echelon_form(self,matrix_rref):
        diagonal = list()
        for i in range(self.k):
            diagonal.append( matrix_rref[i,i] )
        if sum(diagonal) == self.k:
            return True
        else:
            return False
    def Transform_echelon_Matrix_mod2(self, x):
        numer, denom = x.as_numer_denom()
        return numer*mod_inverse(denom,self.modulus) % self.modulus
    def echelon_form(self,matrix):
        matrix_rref = matrix.rref( iszerofunc = lambda x: x % self.modulus == 0)[0].applyfunc(lambda x:  self.Transform_echelon_Matrix_mod2(x)   )
        if self.is_echelon_form(matrix_rref):
            return matrix_rref, True
        else:
            return matrix_rref,False
    def Generate_S_invertible(self):
        condition = True
        while condition:
            permutation_input = int(self.k * self.k)
            S = np.random.permutation(permutation_input).reshape(self.k, self.k)
            S = np.mod(S, self.modulus) 
            if np.linalg.det(S.astype(float)) != 0:
                condition = False
        return S
    def generate_permutation_matrix(self):
        identity_matrix = np.eye(int(self.n), dtype = int)
        permutation = np.random.permutation(self.n)
        permutation_matrix = identity_matrix[permutation]
        return permutation_matrix 
    def generate_public_key(self):
        public_key_dict, parity_matrix_dict  = self.read_text_files() 
        public_key_arrays, parity_matrix_arrays, generator_public_keys = dict() , dict(), dict()
        for key in public_key_dict:
            public_key_arrays[key] = np.array( public_key_dict[key]).astype(int)
        for key in parity_matrix_dict:
            parity_matrix_arrays[key] = np.array(parity_matrix_dict[key]).astype(int)

        for (generator_key, generator_matrix), (parity_key,parity_matrix) in zip(public_key_arrays.items(), parity_matrix_arrays.items()):
            self.k, self.n =  generator_key
            # verify if  se G.H^T = 0
            validate = np.mod(np.dot(generator_matrix,np.transpose(parity_matrix)), self.modulus )
            if (validate == np.zeros( (self.k, self.n - self.k ), dtype= int) ).all():
                #print("True")
                pass
            else:
                pass
                #print("False")
            control = True
            while control:
                    S = self.Generate_S_invertible() 
                    P = self.generate_permutation_matrix()
                    Public_key = np.mod(np.dot( np.mod( np.dot(S,generator_matrix )  , 2)  , P), 2).astype(int)
                    sympy_matrix = Matrix(Public_key)
                    # verify if public key is full rank 
                    echelon_matrix, verify =  self.echelon_form(sympy_matrix)
                    if verify == True:
                        control = False
                        generator_public_keys[(self.k, self.n)] = Public_key
                    else:
                        control = True
        return generator_public_keys  
    def encrypt(self):
        Public_keys                        = dict()
        for keys in self.generate_public_key() :
            self.k, self.n                 = keys
            matrix                         = self.generate_public_key()[keys]
            # Choose secret message
            self.original_message          = np.random.randint(low = 0, high = 1 + 1 , size = self.k ).astype(np.int32)
            error_locations                = random.sample([i for i in range(self.n)], self.t)
            self.Error                     = np.zeros(shape = self.n, dtype = np.int32)
            for loc in error_locations:
                self.Error[loc]            = 1
            self.original_codeword         =  np.mod(np.dot(self.original_message,matrix), self.modulus)
            self.ciphertext                =  np.bitwise_xor(self.original_codeword,self.Error)
            ciphertext_tuple               =  tuple(self.ciphertext)
            Public_keys[ciphertext_tuple, self.t]  =  matrix 
            print("message: ", self.original_message )
            print("self.ciphertext : ", self.ciphertext  )
            
        #print(Public_keys)
        keys = Public_keys.keys()
        matrix  = Public_keys.values()
        #We encrypt the message 
        dir_path = os.path.dirname(os.path.abspath(__file__))
        output_file_path = os.path.join(dir_path, f'Sent ({self.k},{self.n},{self.t}).txt')
        with open(output_file_path, 'w') as f:
            for key, matrix in Public_keys.items():
                ciphertext, t = key
                ciphertext_str = ' '.join(map(str, ciphertext))
                f.write(ciphertext_str + '\n')
                f.write(str(t) + '\n')
                for row in matrix:
                    f.write(' '.join(map(str, row)) + '\n')
        return Public_keys       
    
encrypt= ENCRYPT()
encrypt.encrypt() 
class ATTACK:
    def __init__(self):
        self.diretorio_script = os.path.dirname(os.path.abspath(__file__))
        self.folder_path = os.path.join(self.diretorio_script, f'results {datetime.now().strftime("%Y-%m-%d")}')
        self.modulus = 2
    def read_file(self):
        # Ensure the folder exists
        if not os.path.exists(self.folder_path):
            os.makedirs(self.folder_path)
        # Get a list of all text files in the specified folder
        self.text_files = glob.glob(os.path.join(self.diretorio_script, "*.txt"))
        
        keys =[]
        matrix = []
        for file_path in self.text_files:
            file_name = os.path.basename(file_path)
            try:
                with open(file_path, "r") as f:
                    for _ in range(2):
                        linha = f.readline().strip()
                        keys.append( list(map(int, linha.split()))  )
                    for linha in f:
                        if linha.strip():
                            matrix.append( list(map(int, linha.split()))  )
            except FileExistsError:
                 print(f"Erro: O arquivo {file_name} não foi encontrado.")
            except Exception as e:
                print(f"Erro ao abrir o arquivo {file_name}: {e}")    
        self.Public_keys = np.array(matrix)
        self.ciphertext, self.t = keys
        self.t = int( self.t[0])
        self.k = self.Public_keys.shape[0]
        self.n = self.Public_keys.shape[1]

        return  self.Public_keys , self.ciphertext, self.t
    def is_echelon_form(self,matrix_rref):
        diagonal = list()
        for i in range(self.k):
            diagonal.append( matrix_rref[i,i] )
        if sum(diagonal) == self.k:
            return True
        else:
            return False    
    def Transform_echelon_Matrix_mod2(self, x):
        numer, denom = x.as_numer_denom()
        return numer*mod_inverse(denom,self.modulus) % self.modulus
    def echelon_form(self,matrix):
        #Find row-reduced echolon form of matrix modulo 2:
        matrix_rref = matrix.rref( iszerofunc = lambda x: x % self.modulus == 0)[0].applyfunc(lambda x:  self.Transform_echelon_Matrix_mod2(x)   )
        if self.is_echelon_form(matrix_rref):
            return matrix_rref, True
        else:
            return matrix_rref,False
    def GaussianEliminationMod2(self, matrix):
        Matrix_A = matrix.copy()
        for j in range(self.k):       
            # look for a pivot
            pivot_i = -1
            for i in range(j,self.k):
                if Matrix_A[i,j] == 1:
                    pivot_i = i
                    break
            assert(Matrix_A[pivot_i,j] == 1)
            # swap rows j and pivot_i 
            if pivot_i != j:
                tmp = Matrix_A[pivot_i,:].copy()
                Matrix_A[pivot_i,:] = Matrix_A[j,:].copy()
                Matrix_A[j,:] = tmp
            # zero out column j in other rows
            for i in range(self.k):
                if i != j and Matrix_A[i,j]==1:
                    Matrix_A[i,:] = np.mod( Matrix_A[i,:] + Matrix_A[j,:], self.modulus )
        return Matrix_A                    
    def verificar_inversa_public_key(self,indices_aleatorios):
        # Converte a matriz para o tipo de dados 'int'
        matrix_I = np.array( self.Public_key )[:, indices_aleatorios].astype(int)
        if np.linalg.det( matrix_I ) != 0:
            return True
        else:
            return False
    def NextConfiguration(self, z, sigma, Algorithm):
        permutation_gives_fullrank_block = False
        while not permutation_gives_fullrank_block:     
            theta = random.sample([i for i in range(self.n)], self.n)
            try:
                G = self.GaussianEliminationMod2(self.Public_keys[:, theta])       
            except:
                pass
            else:
                permutation_gives_fullrank_block = True
        # update z
        zz = [z[i] for i in theta ]
        zz = np.array(zz)
        #zz = z[theta]
        z = np.mod(zz + zz[:self.k].dot( G ) , self.modulus)   # array
        # update sigma
        sigma = sigma[theta]
        return G, z, sigma, theta[:self.k]
    def is_invertible_mod2(self,matrix):
        det = np.linalg.det(matrix) % self.modulus  
        return det != 0
    
    def message_recovered(self,ciphertext, error,G, information_set_decoding):
        self.G = G
        self.ciphertext = ciphertext
        self.recover_codeword = np.mod((self.ciphertext - error), self.modulus ) # codeword recuperado 
        G_I = self.G[:,information_set_decoding ]
        self.recover_codeword_position_I =  self.recover_codeword [[information_set_decoding]] 
        inverse_matrix = Matrix(G_I).inv_mod( self.modulus)
        M_inv_mod_2_np = np.array(inverse_matrix).astype(int)
        recovered_message = (np.mod( np.dot(self.recover_codeword_position_I,inverse_matrix ), self.modulus ))[0].tolist()
        return recovered_message
    
    def DecodeError_Leon(self, ciphertext, G):
        self.ciphertext = ciphertext
        self.public_matrix = G
        assert(len(self.ciphertext) == self.n)
        z = self.ciphertext.copy()
        sigma = np.arange(self.n)
        found = False
        while True:
            G, z, sigma, information_set_decoding = self.NextConfiguration(z, sigma,"Leon")
            # check for success
            assert(all(z[: self.k]==0))
            for r in range(self.p + 1):
                for m_support in list(combinations([i for i in range(self.k)], r)):
                    m = np.zeros(self.k, dtype = np.int32)
                    for loc in m_support:
                        m[loc] = 1
                    
                    q = np.mod(z + m.dot(G), self.modulus)
                    # check the first l non-pivot columns first
                    if sum(q[self.k : self.k + self.l]) <= self.p - r:
                        # then check remaining n-k-l columns
                        assert(sum(q) == r + sum(q[self.k : self.k + self.l]) + sum(q[self.k + self.l:]))
                        if sum(q[self.k + self.l:]) == self.t - r - sum(q[self.k : self.k + self.l]):
                            found = True
                            break
                        #print("leon", self.Leon )
                if found:
                    break
            if found:
                break
        
        # un-permute q
        e = np.zeros(self.n, dtype=np.int32)
        for i, loc in enumerate(sigma):
            e[loc] = q[i]  
        return e, information_set_decoding 
    def execute_Leon(self, G, ciphertext):
        self.resultLeon = dict()
        start_time = time.time()
        start_process_time = time.process_time()
        initial_memory = memory_usage()[0]
        self.G = G
        error_Leon, information_set_decoding_Leon                       =  self.DecodeError_Leon(self.ciphertext,self.Public_keys)
        message = self.message_recovered(ciphertext, error_Leon,G, information_set_decoding_Leon)
        #print("message leon:\t", message)
        end_time = time.time()
        end_process_time = time.process_time()
        final_memory   = memory_usage()[0]
        execution_time = end_time - start_time
        cpu_time       = end_process_time - start_process_time
        memory_used    = final_memory - initial_memory
        self.resultLeon["Times"]   = f"{execution_time:.2f}"
        self.resultLeon["Process Times"]     = f"{cpu_time:.2f}"
        self.resultLeon["Memory(MB)"]  = f"{memory_used:.2f}"
        print("Leon message recovered_\t", message)
        return self.resultLeon
     
    def DecodeError_LeeBrickell(self, ciphertext, G):
        self.ciphertext = ciphertext
        self.public_matrix = G
        assert(len(self.ciphertext  ) == self.n)
        z = self.ciphertext.copy()
        sigma = np.arange(self.n)
        found = False
        while True:
            G, z, sigma,information_set_decoding = self.NextConfiguration(z, sigma, "LeeBrickell")
            # check for success
            assert(all(z[:self.k]==0))
            for r in range(self.p + 1):
                for m_support in list(combinations([i for i in range(self.k)], r)):
                    m = np.zeros(self.k, dtype=np.int32)
                    for loc in m_support:
                        m[loc] = 1
                    
                    q = np.mod(z + m.dot(G), self.modulus)
                    
                    assert(sum(q) == r + sum(q[self.k:]))
                    if sum(q[self.k:]) == self.t - r:
                        found = True
                        break
                if found:
                    break
            if found:
                break
        
        # un-permute q
        e = np.zeros(self.n, dtype=np.int32)
        for i, loc in enumerate(sigma):
            e[loc] = q[i]  
        return e, information_set_decoding
    def execute_LeeBrickell(self, G, ciphertext):
        self.ciphertext = ciphertext 
        self.resultLeeBrickell = dict()
        start_time = time.time()
        start_process_time = time.process_time()
        initial_memory = memory_usage()[0]
        self.G = G
        error_LeeBrickell, information_set_decoding_brickell            = self.DecodeError_LeeBrickell(self.ciphertext,self.Public_keys)
        message = self.message_recovered(ciphertext, error_LeeBrickell,G, information_set_decoding_brickell)
        end_time = time.time()
        end_process_time = time.process_time()
        final_memory = memory_usage()[0]
        execution_time = end_time - start_time
        cpu_time = end_process_time - start_process_time
        memory_used = final_memory - initial_memory
        self.resultLeeBrickell["Times"]   = f"{execution_time:.2f}"
        self.resultLeeBrickell["Process Times"]     = f"{cpu_time:.2f}"
        self.resultLeeBrickell["Memory(MB)"]  = f"{memory_used:.2f}"
        print("LeeBrickell message recovered:\t", message)
        return self.resultLeeBrickell
    
    def DecodeError_McEliece(self,ciphertext, G):
        self.public_matrix = G
        self.ciphertext = ciphertext
        assert(len(self.ciphertext) == self.n)
        z = self.ciphertext.copy()
        sigma = np.arange(self.n)
        n_loops = 0
        while True:
            n_loops += 1
            G, z, sigma, I = self.NextConfiguration(z, sigma, "McEliece")
            # check for success
            assert(all(z[:self.k]==0))
            if sum(z[self.k:]) == self.t:
                break        
        # un-permute z
        e = np.zeros(self.n, dtype=np.int32)
        for i, loc in enumerate(sigma):
            e[loc] = z[i] 
        return e,I
    def execute_McElice(self, G, ciphertext):
        self.resultMcEliece = dict()
        start_time = time.time()
        start_process_time = time.process_time()
        initial_memory = memory_usage()[0]
        control = True
        while control:
            error_McEliece, McEliece_information_set_decoding = self.DecodeError_McEliece(ciphertext, G)
            matrix = G[:,McEliece_information_set_decoding ] 
            if self.is_invertible_mod2(matrix) == True:
                self.recover_codeword = np.mod((ciphertext - error_McEliece), self.modulus ) # codeword recuperado 
                self.recover_codeword_position_I =  self.recover_codeword [[McEliece_information_set_decoding]] 
                inverse_matrix = Matrix(matrix).inv_mod( self.modulus)
                recovered_message = (np.mod( np.dot(self.recover_codeword_position_I,inverse_matrix ), self.modulus ))[0].tolist() 
                mG = np.mod(np.dot(recovered_message,G),2) 
                recov_ciphertext = np.bitwise_xor( mG  ,  error_McEliece)
                if ( recov_ciphertext == ciphertext).all():
                    print("McEliece Message recovered:\t ", recovered_message )
                    control = False
                else:
                    control = True

        end_time = time.time()
        end_process_time = time.process_time()
        final_memory = memory_usage()[0]
        execution_time = end_time - start_time
        cpu_time = end_process_time - start_process_time
        memory_used = final_memory - initial_memory
        self.resultMcEliece["Times"]   = f"{execution_time:.2f}"
        self.resultMcEliece["Process Times"]     = f"{cpu_time:.2f}"
        self.resultMcEliece["Memory(MB)"]  = f"{memory_used:.2f}"
        return  self.resultMcEliece
    
    def graphic(self, data, algorithm):
        data_float = {key: float(value) for key, value in data.items()}
        data_left = {k: v for k, v in data_float.items() if k != 'Memory(MB)'}
        data_right = {'Memory(MB)': data_float['Memory(MB)']}
        # Dados fornecidos
        # Posições personalizadas para as barras
        bar_width = 0.4
        positions_left = np.arange(len(data_left)) * (bar_width + 0.3)
        positions_right = np.array([max(positions_left) + bar_width + 0.3])

        # Criando o gráfico de barras com posições personalizadas
        fig, ax1 = plt.subplots(figsize=(10, 6))

        # Barras para o eixo y esquerdo
        bars_left = ax1.bar(positions_left, data_left.values(), color=['blue', 'green'], width=bar_width, label=list(data_left.keys()))

        # Barras para o eixo y direito
        ax2 = ax1.twinx()
        bars_right = ax2.bar(positions_right, data_right.values(), color='red', width=bar_width, label=list(data_right.keys()))

        # Adicionando rótulos de valores nas barras do eixo esquerdo
        for bar in bars_left:
            yval = bar.get_height()
            ax1.text(bar.get_x() + bar.get_width()/2, yval * 1.01, round(yval, 2), ha='center', va='bottom')
        # Adicionando rótulos de valores nas barras do eixo direito
        for bar in bars_right:
            yval = bar.get_height()
            ax2.text(bar.get_x() + bar.get_width()/2, yval * 1.01, round(yval, 2), ha='center', va='bottom')

        # Ajustando os rótulos e título
        ax1.set_xlabel(f'{algorithm}')  # Rótulo do eixo x
        ax1.set_ylabel('Seconds')  # Rótulo do eixo y esquerdo
        ax2.set_ylabel('MB')  # Rótulo do eixo y direito
        # Ajustando os rótulos do eixo x para corresponder às posições
        ax1.set_xticks(np.concatenate((positions_left, positions_right)))
        ax1.set_xticklabels(list(data_left.keys()) + list(data_right.keys()))

        # Adicionando legendas
        bars = bars_left + bars_right
        labels = list(data_left.keys()) + list(data_right.keys())
        ax1.legend(bars, labels, loc='upper center', bbox_to_anchor=(0.5, -0.1), ncol=3)
        file_path = os.path.join(self.folder_path, f'Metrics_{algorithm}.png')
        fig.savefig(file_path, dpi = 300,bbox_inches='tight')
        plt.tight_layout()
        #plt.show()

    def main(self):
        self.l = 3
        self.p = 3
        self.Public_keys , self.ciphertext, self.t = self.read_file() 
        result_McEliece= self.execute_McElice(self.Public_keys, self.ciphertext)
        result_leeBrickell = self.execute_LeeBrickell(self.Public_keys, self.ciphertext)
        result_leon = self.execute_Leon(self.Public_keys, self.ciphertext)
        algorithms = ["McEliece", "Lee Brickell", "Leon"]
        data = [result_McEliece, result_leeBrickell, result_leon]
        report = {}
        for alg, data in zip(algorithms, data):
            report[f"{alg}"] = data
            self.graphic(data, alg)
        df = pandas.DataFrame(report )
        df_transposed = df.transpose()
        print(df_transposed) 
    
# Criar uma instância da classe e chamar o método read_file
attack = ATTACK()
attack.main()

