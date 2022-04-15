import json

def get_function_from_abi(json_object, key, value, ret):
    try:
        json_object = json.loads(json_object)
        for dict in json_object:
            if dict[key] == value:
                if ret in dict.keys():
                    return dict[ret]
                else:
                    return ""
    except:
        return ""

def get_function_visibility_from_abi():
    #Wrtie Code
    return 1