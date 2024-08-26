from z3 import *

def bv_sort(max_value, ctx=None):
    return BitVecSort(len(bin(max_value)) - 2, ctx=ctx)


# wrapper around a object map for the parsed model
# this is used to pass the model to the synthesizer
# (necessary, as Model->Program parser needs evaluation methods)
# warning: do not use the setter of the model attribute
class ParsedModelWrapper:
    def __init__(self, model):
        self.model = model

    def __getitem__(self, key):
        return self.model[str(key)]

    def evaluate(self, expr, model_completion=True):
        return self.model[str(expr)]
    


def parse_smt2_output(ctx, model_string: str):
    # create always True and False bool z3 value constants
    b = Bool('p')
    z3_true = simplify(b == b)
    z3_false = simplify(Not(z3_true))

    model = {}
    # since linebreaks may be arbitrary, just remove them
    model_string = model_string.replace("\n", "").strip()

    # while we are not at the closing parenthesis of the model
    while not model_string.strip() == ")":
        if not model_string.startswith('(define-fun'):
            # cut off first character, hopefully just spaces; or "(model"
            model_string = model_string[1:]
            continue

        # cut off the define-fun
        model_string = model_string[len('(define-fun'):].strip()

        # get the name of the variable
        var_name, model_string = model_string.split(" ", 1)

        model_string = model_string.strip()

        # we expect empty function types
        if not model_string.startswith("()"):
            print("Expected empty function type")
            return None

        model_string = model_string[len("()"):].strip()

        # parse type and value
        if model_string.startswith("(_ BitVec"):
            # cut off the type
            model_string = model_string[len("(_ BitVec"):].strip()

            # get the bit width
            bit_width, model_string = model_string.split(")", 1)
            bit_width = int(bit_width)

            # cut off the space
            model_string = model_string.strip()

            # get the value
            value, model_string = model_string.split(")", 1)
            value = value.strip()

            # value has prefix #b
            value = value[len("#b"):]

            # convert to z3 value
            model[var_name] = BitVecVal(int(value, 2), bit_width, ctx=ctx)
        elif model_string.startswith("Bool"):
            # cut off the type
            model_string = model_string[len("Bool"):].strip()

            # get the value
            value, model_string = model_string.split(")", 1)
            value = value.strip()

            # convert to z3 value
            model[var_name] = z3_true if value == "true" else z3_false
        elif model_string.startswith("Int"):
            # cut off the type
            model_string = model_string[len("Int"):].strip()

            # get the value
            value, model_string = model_string.split(")", 1)
            value = value.strip()

            # convert to z3 value
            model[var_name] = IntVal(int(value), ctx=ctx)
        else:
            print("Unknown type in model: " + model_string)
            exit(1)

        # store value in model with pipes, as needed sometimes(?)
        model[f'|{var_name}|'] = model[var_name]
    
    return ParsedModelWrapper(model)
