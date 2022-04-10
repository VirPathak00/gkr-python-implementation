from calendar import leapdays
from math import log2
from random import randint
from sumcheck import *



#the chi functions we need for multilinear extensions (see Thaler's section on MLE)
def chi(w, x):
  prod = 1
  for i in range(len(x)):
    prod = prod * (x[i]*w[i] + (1 - x[i])*(1 - w[i]))
  return prod  


#find multilinear extension
def ext(f, variable_length, x):
  acc = 0
  w = Convert(generate_binary_strings(variable_length))
  for i in range(len(w)):
    w[i] = Convert(w[i])
    for j in range(len(w[i])):
      w[i][j] = int(w[i][j])
  for k in range(len(w)):  
    acc += f(w[k])*(chi(w[k],x))
  return acc % p


#define a binary tree to represent our arithmetic circuit. A value of '+' in the node will represent addition, while '*' will represent multiplication
class Node:
  def __init__(self, binary_index, value, left=None, right=None):
    self.binary_index = binary_index
    self.value = value
    self.left = left
    self.right = right


class Circuit:
  def __init__(self, layer_sizes=[1, 2, 2]):
    self.layers = list(map(lambda size: [None] * (2 ** size + 3), layer_sizes))
  
  def get_node(self, layer, index):
    return self.layers[layer][index]

  def add_node(self, layer, index, binary_index, value, left=None, right=None):
    self.layers[layer][index] = Node(binary_index, value, left, right)
  
  def add_func(self, layer,index,func):
    self.layers[layer][index] = func

  def depth(self):
    return len(self.layers)

  def layer_length(self, layer):
    return len(self.layers[layer])
  
  def layer_bits(self, layer):
    return int(log2(self.layer_length(layer)))
  
  def add(self, layer, index, left, right):
    node = self.get_node(layer, index)
    return int((node.left == left) and (node.right == right) and (node.value == '+'))

  def mult(self, layer, index, left, right):
    node = self.get_node(layer, index)
    return int((node.left == left) and (node.right == right) and (node.value == '*'))

def get_binary_index(Node):
  return Node.binary_index

def valueataNode(Node):
  if Node.left == None and Node.right == None:
    return Node.value
  elif Node.value == '*':
    return valueataNode(Node.left)*valueataNode(Node.right)
  elif Node.value == '+':
    return valueataNode(Node.left) + valueataNode(Node.right)

def Wpoly(circuit, i, index):
  return valueataNode(circuit.get_node(i, index))



def circuit_add(circuit,layer, w_list):
  left_node = circuit.get_node(layer, w_list[1])
  right_node = circuit.get_node(layer, w_list[2])
  return circuit.add(layer, w_list[0], left_node, right_node)

def circuit_mult(circuit,layer, w_list):
  left_node = circuit.get_node(layer, w_list[1])
  right_node = circuit.get_node(layer, w_list[2])
  return circuit.mult(layer, w_list[0], left_node, right_node)

def ell(p1, p2, t):
  consts = p1
  output = [0]*len(p2)
  other_term = [0]*len(p2)
  for i in range(len(p2)):
    other_term[i] = p2[i] - consts[i]
  for i in range(len(p2)):
    output[i] = consts[i] + t*other_term[i]
  return output







def gkr(D, circuit): 

  m = [0]*circuit.depth()
  z = [0]*circuit.depth()
  z[0] = [0]*int((circuit.layer_length(0)-3)/2)
  for i in range(len(z[0])):
    z[0][i] = randint(0,p-1)
  m[0] = ext(D, (circuit.layer_length(0) - 3)/2, z[0])
#-2 spot is mult, -1 spot is add
  for i in range(circuit.depth() - 1):
    def f(x):
      b = x[:(len(x)//2)]
      c = x[len(x)//2:]
      return  (ext(circuit.get_node(i, -1), (circuit.layer_length(i+1) - 3) + ((circuit.layer_length(i) - 3)/2), z[i] + b + c) * (ext(circuit.get_node(i+1, -3), (circuit.layer_length(i+1) - 3)/2, b) + ext(circuit.get_node(i+1, -3), (circuit.layer_length(i+1) - 3)/2, c)) + ext(circuit.get_node(i, -2), (circuit.layer_length(i+1) - 3) + (circuit.layer_length(i) - 3)/2, z[i] + b + c) * (ext(circuit.get_node(i+1, -3), (circuit.layer_length(i+1) - 3)/2, b) * ext(circuit.get_node(i+1, -3), (circuit.layer_length(i+1) - 3)/2, c))) % p
    val = sumcheck(m[i], f, int((circuit.layer_length(i+1) - 3)))
    if(val == False):
      return False
    else:
      r = get_r()
      b_star = r[0: int((circuit.layer_length(i + 1) - 3)/2)]
      c_star = r[int((circuit.layer_length(i+1) - 3)/2):int((circuit.layer_length(i+1) - 3))]

      q_at_zero = ext(circuit.get_node(i+1,-3), (circuit.layer_length(i+1) - 3)/2 ,ell(b_star, c_star, 0))
      q_at_one = ext(circuit.get_node(i+1, -3), (circuit.layer_length(i+1) - 3)/2 ,ell(b_star, c_star, 1))

      def modified_f():
        return  ext(circuit.get_node(i, -1), (circuit.layer_length(i+1) - 3) + ((circuit.layer_length(i) - 3)/2), z[i] + b_star + c_star) * (q_at_zero + q_at_one) + ext(circuit.get_node(i, -2), (circuit.layer_length(i+1) - 3) + (circuit.layer_length(i) - 3)/2, z[i] + b_star + c_star) * (q_at_zero * q_at_one) % p
      if f(b_star + c_star) != modified_f():
        return False
      else:
        r_star = randint(0, p-1)
        z[i+1] = ell(b_star, c_star, r_star)
        m[i+1] = ext(circuit.get_node(i+1, -3), int((circuit.layer_length(i+1) - 3)/2), ell(b_star, c_star, r_star))
  
  if m[circuit.depth() - 1] != ext(circuit.get_node(circuit.depth() - 1, -3), (circuit.layer_length(circuit.depth() - 1) - 3)/2, z[circuit.depth() - 1]):
    return False
  return True


#test circuit
c = Circuit()
a1 = Node([0],36)
a2 = Node([1],6)
b1 = Node([0,0], 9)
b2 = Node([0,1], 4)
b3 = Node([1,0], 6)
b4 = Node([1,1], 1)
c1 = Node([0,0],3)
c2 = Node([0,1], 2)
c3 = Node([1,0],3)
c4 = Node([1,1],1)


# W0
c.add_node(0, 0, [0], 36, left=b1, right=b2)
c.add_node(0, 1, [1], 6, left=b3, right=b4)

def W0func(arr):
  if(arr == [0]):
    return 25
  elif (arr == [1]):
    return 160

c.add_func(0, 2, W0func)

def multlayerzero(arr):
  if arr == [0,0,0,0,1]:
    return 1
  elif arr == [1,1,0,1,1]:
    return 1
  else:
    return 0

def addlayerzero(arr):
  return 0
c.add_func(0,3,multlayerzero)
c.add_func(0,4,addlayerzero)


# W1
c.add_node(1, 0, [0,0], 9, left=c1, right=c1)
c.add_node(1, 1, [0,1], 4, left=c2, right=c2)
c.add_node(1, 2, [1,0], 6, left=c2, right=c3)
c.add_node(1, 3, [1,1], 1, left=c4, right=c4)

def W1Func(bitstring):
  if bitstring == [0,0]:
    return 1
  elif bitstring == [0,1]:
    return 25
  elif bitstring == [1,0]:
    return 40
  elif bitstring == [1,1]:
    return 4
c.add_func(1, 4, W1Func)

def multlayerone(arr):
  if arr == [0,0,0,0,0,0]:
    return 1
  elif arr == [0,1,0,1,0,1]:
    return 1
  elif arr == [1,0,0,1,1,0]:
    return 1
  elif arr == [1,1,1,1,1,1]:
    return 1
  else:
    return 0

def addlayerone(arr):
  return 0

c.add_func(1,5,multlayerone)
c.add_func(1,6,addlayerone)

# W2
c.add_node(2, 0, [0,0], 3)
c.add_node(2, 1, [0,1], 2)
c.add_node(2, 2, [1,0], 3)
c.add_node(2, 3, [1,1], 1)

def W2func(bitstring):
  if bitstring == [0,0]:
    return 1
  elif bitstring == [0,1]:
    return 5
  elif bitstring == [1,0]:
    return 8
  elif bitstring == [1,1]:
    return 2
c.add_func(2, 4, W2func)

def multlayertwo(arr):
  return 0
def addlayertwo(arr):
  return 0

c.add_func(2,5,multlayertwo)
c.add_func(2,6,addlayertwo)

def D_func(arr):
  if arr == [0]:
    return 25
  elif arr == [1]:
    return 160
def D_func_ext(arr):
  return ext(D_func, 1, arr)

print(gkr(D_func_ext, c))

