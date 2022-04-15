import random


def mut_bool(value):
    result = True
    options = [True, False]
    mut = random.choice(options)
    if mut is True:
        result = not value
    return result


def mut_uint(value):
    new_b = 0
    for x in range(value.bit_length()):
        new_b |= bool(random.random()>0.7) << x
    return new_b

def mut_int(value):
    new_b = 0
    for x in range(value.bit_length()):
        new_b |= bool(random.random()>0.7) << x
    if value < 0:
        new_b = -new_b
    return new_b


def mut_bytes(value):
    new_value = [ord(c) for c in value]
    options = ['0','1','2','3','4','5','6','7','8','9','a','b','c','d','e','f',]
    value_to_add = random.choice(options)
    new_value.insert(random.randint(2, len(new_value)), ord(value_to_add))
    value_to_add = random.choice(options)
    new_value.insert(random.randint(2, len(new_value)), ord(value_to_add))
    new_value.pop(random.randint(2, len(new_value)-1))
    new_value.pop(random.randint(2, len(new_value)-1))
    result = ''.join(map(chr, new_value))
    return result


def mut_address(value):
    return value


def mut_array(type,length,data):
    array = []

    data_type = ''
    data_length = ''

    for i in range(len(type)):
        if type[i].isdigit():
            data_length = data_length + type[i]
        else:
            data_type = data_type + type[i]
    # print(data_type)
    # print(int(data_length))

    for i in range(length):
        if data_type == 'uint':
            array.append(mut_uint(data[i]))


        elif data_type == 'int':
            array.append(mut_int(data[i]))

        elif data_type == 'bool':
            array.append(mut_bool(data[i]))

        elif data_type == 'address':
            array.append(mut_address(data[i]))

        elif data_type == 'bytes':
            array.append(mut_bytes(data[i]))
    return array


def mut_string(value):
    new_value = [ord(c) for c in value]
    value_to_add = random.randint(65, 122)
    new_value.insert(random.randint(1,len(new_value)),value_to_add)
    result = ''.join(map(chr,new_value))
    return result


def mut_input(input_args, values):
    old_input_seq = values
    mut_input_seq = []
    mutation_mask = [0]*len(input_args)
    for i in mutation_mask:
        rand = random.randint(1, 100)
        if rand > 40:
            mutation_mask[i] = 1


    for i in range(len(input_args)):
        if mutation_mask[i] == 0:
            mut_input_seq.append(old_input_seq[i])
            continue
        input_type = input_args[i]
        input_value = old_input_seq[i]

        data_type = ''
        data_length = ''

        inp = input_type.split('[')[0]
        array_length = 0

        try:
            #print(inp)
            if input_type[-1] == ']':
                array_length = input_type.split('[')[1]
                if array_length == ']':
                    array_length = len(input_value)
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
                mut_input_seq.append(mut_uint(input_value))

            elif data_type == 'int':
                mut_input_seq.append(mut_int(input_value))

            elif data_type == 'bool':
                mut_input_seq.append(mut_bool(input_value))

            elif data_type == 'address':
                mut_input_seq.append(mut_address(input_value))

            elif data_type == 'string':
                mut_input_seq.append(mut_string(input_value))

            elif data_type == 'bytes':
                mut_input_seq.append(mut_bytes(input_value))
        else:
            mut_input_seq.append(mut_array(inp,array_length,input_value))
    return mut_input_seq


#print(mut_input(['uint8','string'],[543,'sjd']))