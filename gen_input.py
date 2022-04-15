import random
import string
from web3 import Web3


def gen_bool():
    options = [True, False]
    return random.choice(options)


def gen_uint(length):
    options = [8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 16, 16, 32 , 64, 127, 255]
    if length == 0 or length == 256:
        return random.randint(0, 2**random.choice(options))
    if length == 128:
        return random.randint(0, 2**random.choice(options[:-1]))
    if length == 64:
        return random.randint(0, 2**random.choice(options[:-2]))
    if length == 32:
        return random.randint(0, 2**random.choice(options[:-3]))
    else:
        return random.randint(0, 2**length-1)


def gen_int(length):
    options = [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 15, 15, 31, 63, 127, 255]
    if length == 0 or length == 256:
        return random.randint(-2**random.choice(options), 2**random.choice(options))
    if length == 128:
        return random.randint(-2**random.choice(options[:-1]), 2**random.choice(options[:-1]))
    if length == 64:
        return random.randint(-2**random.choice(options[:-2]), 2**random.choice(options[:-2]))
    if length == 32:
        return random.randint(-2**random.choice(options[:-3]), 2**random.choice(options[:-3]))
    else:
        return random.randint(-2**(length-1)-1, 2**(length-1)-1)


def gen_bytes(length):
    value = "0x"
    if length == 0:
        length = random.randint(1,30)
    options = ['0','1','2','3','4','5','6','7','8','9','a','b','c','d','e','f',]
    for i in range(length*2):
        value = value + (random.choice(options))
    return value


def gen_address(addressArray):
    options = addressArray
    if len(addressArray) == 0:
        options = ['0x96780224CB07A07C1449563C5dfc8500fFa0Ea2A', '0xf97DdC7b1836c7bb14cD907EF9845A6c028428f4']
    choice = random.choice(options)
    return Web3.toChecksumAddress(choice)


def gen_array(type,length,addressArray):
    array = []
    if length == 0:
        length = random.randint(2, 10)

    data_type = ''
    data_length = ''

    for i in range(len(type)):
        if type[i].isdigit():
            data_length = data_length + type[i]
        else:
            data_type = data_type + type[i]
    #print(data_type)
    #print(int(data_length))

    #data_length = int(data_length)

    if data_length == '':
        data_length = 256
    else:
        data_length = int(data_length)

    for i in range(length):
        if data_type == 'uint':
            array.append(gen_uint(data_length))

        elif data_type == 'int':
            array.append(gen_int(data_length))

        elif data_type == 'bool':
            array.append(gen_bool())

        elif data_type == 'address':
            array.append(gen_address(addressArray))

        elif data_type == 'bytes':
            array.append(gen_bytes(data_length))

    return array


def gen_string():
    #if length == 0:
    length = random.randint(1, 10)
    letters = string.ascii_letters
    return ''.join(random.choice(letters) for i in range(length))


def gen_input(input_args, constrtructor, addressArray):
    input_seq = []
    for input_type in input_args:
        data_type = ''
        data_length = ''

        inp = input_type.split('[')[0]
        array_length = 0

        try:
            #print(inp)
            if input_type[-1] == ']':
                array_length = input_type.split('[')[1]
                if array_length == ']':
                    array_length = random.randint(1, 5)
                else:
                    array_length = int(array_length[:-1])
                #print(array_length)
        except Exception as e:
            print(e)

        for i in range(len(inp)):
            if inp[i].isdigit():
                data_length = data_length + inp[i]
            else:
                data_type = data_type + inp[i]
        if array_length == 0:
            if data_length == '':
                data_length = 0
            else:
                data_length = int(data_length)

            if data_type == 'uint':
                input_seq.append(gen_uint(data_length))

            elif data_type == 'int':
                input_seq.append(gen_int(data_length))

            elif data_type == 'bool':
                input_seq.append(gen_bool())

            elif data_type == 'address':
                if constrtructor is True:
                    input_seq.append(addressArray)
                else:
                    input_seq.append(gen_address(addressArray))

            elif data_type == 'string':
                input_seq.append(gen_string())

            elif data_type == 'bytes':
                input_seq.append(gen_bytes(data_length))
        else:
            input_seq.append(gen_array(inp,array_length,addressArray))
    return input_seq






# print(gen_string())
# print(gen_bool())
# print(gen_uint(0))
# print(gen_int(0))
#
# print(gen_bytes(8))
