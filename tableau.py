
MAX_CONSTANTS = 10
RESERVED_SYMBOLS = set(["x", "y", "z", "w", "p", "q", "r", "s", "P", "Q", "R", "S"])


# Parse a formula, consult parseOutputs for return values.
def parse(fmla):
    #print(fmla)  # Debugging output to trace steps
    if not fmla:
        return 0  # "not a formula"

    # Check if it's a propositional atom
    if fmla in ["p", "q", "r", "s"]:
        return 6  # "a proposition"

    # Check if it's a predicate atom
    if is_predicate_atom(fmla):
        return 1  # "an atom"

    # Check for negation
    if fmla[0] == "~":
        # Parse the remaining formula recursively
        subformula = fmla[1:]  # Strip the leading "~"
        sub_result = parse(subformula)
    
        # Check if the subformula is valid
        if sub_result in [6, 7, 8]:  # Propositional formulas
            return 7  # "a negation of a propositional formula"
        elif sub_result in [1, 2, 3, 4, 5]:  # First-order formulas
            return 2  # "a negation of a first order logic formula"
    
        # If the subformula is invalid, return "not a formula"
        return 0  # "not a formula"

            

    # Check for quantifiers (Evar, Avar)
    if len(fmla) > 2 and fmla[:2] in [f"E{v}" for v in ["x", "y", "z", "w"]] + [f"A{v}" for v in ["x", "y", "z", "w"]]:
        variable = fmla[1]
        if variable in ["x", "y", "z", "w"]:
            subformula = fmla[2:]
            sub_result = parse(subformula)
            if sub_result != 0:
                if fmla[0] == "E":
                    return 4  # "an existentially quantified formula"
                elif fmla[0] == "A":
                    return 3  # "a universally quantified formula"
        return 0  # Invalid quantifier usage

    # Check for binary connectives
    if fmla.startswith("(") and fmla.endswith(")"):
        left, right, main_connective = find_main_connective(fmla)
        if left and right and main_connective:
            left_result = parse(left)
            right_result = parse(right)
            if left_result != 0 and right_result != 0:
                if left_result in [6, 8,7] and right_result in [6, 8,7]:
                    return 8  # "a binary connective propositional formula"
                elif left_result in [1,2,3,4,5] and right_result in [1,2,3,4,5]:
                    return 5  # "a binary connective first order formula"
        return 0  # Invalid binary connective

    # If none of the above, it's not a formula
    return 0

def is_predicate_atom(fmla):
    if len(fmla) < 5 or fmla[0] not in ["P", "Q", "R", "S"]:
        return False
    if fmla[1] != "(" or fmla[-1] != ")":
        return False
    vars_inside = fmla[2:-1].split(",")
    return len(vars_inside) == 2 and all(var in ["x", "y", "z", "w"] for var in vars_inside)

def find_main_connective(fmla):
    depth = 0
    for i in range(1, len(fmla) - 1):  # Skip outer parentheses
        if fmla[i] == "(":
            depth += 1
        elif fmla[i] == ")":
            depth -= 1
        elif depth == 0:  # At top level
            for connective in ["/\\", "\\/", "=>"]:
                if fmla[i:i + len(connective)] == connective:
                    # Split the formula at the connective
                    left = fmla[1:i]
                    right = fmla[i + len(connective):-1]
                    return left, right, connective
    return None, None, None  # No main connective found

# Return the LHS of a binary connective formula
def lhs(fmla):
    left, _, _ = find_main_connective(fmla)
    return left

# Return the connective symbol of a binary connective formula
def con(fmla):
    _, _, connective = find_main_connective(fmla)
    return connective

# Return the RHS symbol of a binary connective formula
def rhs(fmla):
    _, right, _ = find_main_connective(fmla)
    return right


# You may choose to represent a theory as a set or a list
def theory(fmla):#initialise a theory with a single formula in it
    return [fmla]

#check for satisfiability
def sat(tableau):
    temp = tableau[0][0]
    queue = [([temp],set())]
    while len(queue)>0:
        #print(queue)
        theory,used_constants = queue.pop()
        #print(theory)
        if fully_expanded(theory) and not is_closed(theory):
            return 1
        
        if fully_expanded(theory) and is_closed(theory):
            continue
        for i, formula in enumerate(theory):
            if not is_literal(formula):
                current = theory.pop(i)
                break
        formula = current
        # Case 1: Conjunction (F1 /\ F2)
        if formula[0] == "(" and con(formula) == "/\\":
            F1 = lhs(formula)  # Left-hand side of the conjunction
            F2 = rhs(formula)  # Right-hand side of the conjunction
            theory.append(F1)
            theory.append(F2)
            queue.insert(0,(theory,used_constants))
            continue

        # Case 2: Negation of Disjunction ~(F1 \/ F2)
        if (formula[0] == "~" and formula[1] == "(") and con(formula[1:]) == "\\/":
            F1 = lhs(formula[1:])  # Left-hand side of the disjunction
            F2 = rhs(formula[1:])  # Right-hand side of the disjunction
            theory.append(f"~{F1}")
            theory.append(f"~{F2}")
            queue.insert(0,(theory,used_constants))
            continue
            
        # Case 3: Negation of Implication ~(F1 => F2)
        if (formula[0] == "~" and formula[1] == "(") and con(formula[1:]) == "=>":
            F1 = lhs(formula[1:])  # Left-hand side of the implication
            F2 = rhs(formula[1:])  # Right-hand side of the implication
            theory.append(F1)
            theory.append(f"~{F2}")
            queue.insert(0,(theory,used_constants))
            continue

        # Case 4: Double Negation ~~F1
        if formula[0] == "~" and formula[1] == "~":
            F1 = formula[2:]  # Remove the two negations
            theory.append(F1)
            queue.insert(0,(theory,used_constants))
            continue

        # Case 1: Disjunction (F1 \/ F2)
        if formula[0] == "(" and con(formula) == "\\/":
            F1 = lhs(formula)  # Left-hand side of the disjunction
            F2 = rhs(formula)  # Right-hand side of the disjunction

            # Create two new, independent theories
            new_theory_1 = theory[:] + [F1]  # Copy the theory and add F1
            new_theory_2 = theory[:] + [F2]  # Copy the theory and add F2

            # Add the new theories to the queue
            queue.insert(0, (new_theory_1,used_constants))
            queue.insert(0, (new_theory_2,used_constants))
            continue
            
        # Case 2: Negation of Conjunction ~(F1 /\\ F2)
        if (formula[0] == "~" and formula[1] == "(") and con(formula[1:]) == "/\\":
            F1 = lhs(formula[1:])  # Left-hand side of the conjunction
            F2 = rhs(formula[1:])  # Right-hand side of the conjunction
            # Branch into two separate theories
            queue.insert(0,([f"~{F1}"]+theory,used_constants))
            queue.insert(0,([f"~{F2}"]+theory,used_constants))
            continue

        # Case 3: Implication (F1 => F2)
        if formula[0] == "(" and con(formula) == "=>":
            F1 = lhs(formula)  # Left-hand side of the implication
            F2 = rhs(formula)  # Right-hand side of the implication
            # Branch into two separate theories
            queue.insert(0,([f"~{F1}"]+theory,used_constants))
            queue.insert(0,([F2]+theory,used_constants))
            continue
            
        # Delta Formulae: Existential Quantifier (ExF(x)) or Negation of Universal Quantifier (~AxF(x))
        if formula[0] == "E" or (formula[0] == "~" and formula[1] == "A"):
            if formula[0] == "E":
                # Extract the quantified variable and inner formula
                variable = current[1]
                inner_formula = current[2:]  # Everything after "Ex"
                #print(inner_formula)
            else:  # Negation of universal quantifier (~AxF(x))
                # Extract the quantified variable and inner formula
                variable = current[2]
                inner_formula = "~"+current[3:]  # Everything after "~Ax"

            # Generate a new constant
            #print(theory)
            new_constant = generate_new_constant(used_constants)  # Generate a constant specific to this branch
            #print(new_constant)
            if new_constant is None:
                return 2  # Indeterminate satisfiability if constants are exhausted

            # Replace the quantified variable with the new constant
            modified_formula = replace_variable_with_constant(inner_formula, variable, new_constant)
            #print(modified_formula)
            # Add the modified formula to the theory
            theory.append(modified_formula)
            #print(theory)
            used_constants.add(new_constant)
            # Check for constant limit in this theory
            if count_constants(theory) > 10:
                return 2  # Exceeded constant limit for this branch
            queue.insert(0,(theory,used_constants))
            # Continue to process the updated theory
            continue
            
        # Gamma Formulae: Universal Quantifier (AxF(x)) or Negation of Existential Quantifier (~ExF(x))
        if current[0] == "A" or (current[0] == "~" and current[1] == "E"):
            # Extract the variable and inner formula
            variable = current[1] if current[0] == "A" else current[2]
            inner_formula = current[2:] if current[0] == "A" else "~" + current[3:]

            # Expand the gamma formula with all 10 constants
            for const in "abcdefghij":
                substituted_formula = replace_variable_with_constant(inner_formula, variable, const)
                theory.append(substituted_formula)  # Add each substitution directly to the theory

            # Do not add the gamma formula back into the queue
            queue.insert(0, (theory, used_constants))  # The used_constants remain unchanged
            continue


        

    # If we exhaust the tableau without finding a satisfiable branch
    return 0  # UNSATISFIABLE

def fully_expanded(theory):
    for formula in theory:
        # If the formula is a tuple (gamma formula), unpack it

        if not is_literal(formula):
            return False

    # If all formulas are fully expanded
    return True


def is_closed_term(formula):
    # Handle negation by stripping the "~" if present
    if formula.startswith("~"):
        formula = formula[1:]

    # Check if it starts with a valid predicate symbol (P, Q, R, S)
    if formula[0] in ["P", "Q", "R", "S"] and "(" in formula and ")" in formula:
        # Extract arguments from the predicate (e.g., P(a,b) -> ["a", "b"])
        arguments = formula[formula.index("(") + 1 : formula.index(")")].split(",")
        
        # Check if there are exactly 2 arguments and they are constants (not variables)
        if len(arguments) == 2 and all(arg.islower() and len(arg) == 1 for arg in arguments) and all(arg not in RESERVED_SYMBOLS for arg in arguments):
            return True

    # If the formula doesn't meet the criteria for a closed term
    return False

    
def is_closed(current):
    literals = set()
    
    for formula in current:
        # If it's a gamma formula (tuple), skip it

        # Handle literals and their negations
        if formula.startswith("~"):
            if formula[1:] in literals:  # Contradiction: ~P and P
                return True
        else:
            if "~" + formula in literals:  # Contradiction: P and ~P
                return True

        # Add the formula to the set of seen literals
        literals.add(formula)
    
    return False
def is_literal(formula):
    # Check for propositional literals
    formula_type = parse(formula)
    if formula_type == 6:
        return True
    if formula_type == 7:
        subformula = formula[1:]  # Strip the leading "~"
        if parse(subformula) == 6:
            return True

    # Check for predicates with constants
    if "(" in formula and ")" in formula:
        # Handle negation
        if formula.startswith("~"):
            formula = formula[1:]  # Strip the leading "~"
        # Check for valid predicate format
        if formula[0] in ["P", "Q", "R", "S"]:  # Predicate starts with P, Q, R, S
            arguments = formula[formula.index("(") + 1 : formula.index(")")].split(",")
            # Ensure arguments are constants
            if len(arguments) == 2 and all(arg.islower() and len(arg) == 1 and arg not in RESERVED_SYMBOLS for arg in arguments):
                return True

    # If none of the above, it's not a literal
    return False
def generate_new_constant(used_constants):
    # Find the first unused constant
    for char in "abcdefghij":
        if char not in used_constants:
            return char
    return None  # No constants available

def replace_variable_with_constant(formula, variable, constant):
    result = []
    i = 0
    while i < len(formula):
        # Detect a quantifier (e.g., Ex or Ax)
        if formula[i:i+2] in [f"E{variable}", f"A{variable}"]:
            result.append(formula[i:i+2])  # Keep the quantifier unchanged
            i += 2
        # Replace the variable inside predicates
        elif formula[i] == variable:
            # Ensure we're replacing a standalone variable (not part of a quantifier)
            if ((i > 0 and formula[i-1] in "(),") or (i < len(formula) - 1 and formula[i+1] in "(),")) and is_free_variable(formula,i):
                result.append(constant)
            else:
                result.append(variable)
            i += 1
        else:
            result.append(formula[i])
            i += 1
    return "".join(result)

def count_constants(theory):
    constants = set()
    for formula in theory:
        for char in formula:
            if char in "abcdefghij":  # Constants are restricted to 'a' through 'j'
                constants.add(char)
    return len(constants)

def is_free_variable(formula, index):
    var = formula[index]
    if var not in {'x', 'y', 'z', 'w'}:
        return False  # The character at index is not a variable

    var_stack = []      # Stack to track quantifiers for the target variable
    scope_stack = []    # Stack to track scopes introduced by '(' and quantifiers

    i = 0
    while i < len(formula):
        # Handle quantifiers: 'Ex' or 'Ax' for the target variable
        if i < len(formula) - 1 and formula[i] in {'E', 'A'} and formula[i+1] == var:
            var_stack.append(var)
            scope_stack.append(var)  # Mark that this scope has a quantifier for 'var'
            i += 2
            continue
        # Handle quantifiers for other variables: skip them
        elif i < len(formula) - 1 and formula[i] in {'E', 'A'} and formula[i+1] != var:
            # Quantifier for another variable, ignore it
            i += 2
            continue
        elif formula[i] == '(':
            scope_stack.append('scope')  # General scope marker
            i += 1
            continue
        # Handle closing parenthesis ')'
        elif formula[i] == ')':
            if scope_stack:
                last_scope = scope_stack.pop()
                if last_scope == var:
                    if var_stack:
                        var_stack.pop()
            i += 1
            continue
        else:
            # If current position is the target index and it's the variable
            if i == index and formula[i] == var:
                # If var_stack is empty, the variable is free
                return len(var_stack) == 0
            i += 1  # Move to the next character

    return False  # Variable not found or not free

parseOutputs = ['not a formula',
                'an atom',
                'a negation of a first order logic formula',
                'a universally quantified formula',
                'an existentially quantified formula',
                'a binary connective first order formula',
                'a proposition',
                'a negation of a propositional formula',
                'a binary connective propositional formula']

satOutput = ['is not satisfiable', 'is satisfiable', 'may or may not be satisfiable']

