from bddl.logic_base import UnaryAtomicFormula, BinaryAtomicFormula
from bddl.backend_abc import BDDLBackend
from bddl.parsing import parse_domain
import bddl.bddl_verification as ver
import copy
import json
import re


*__, domain_predicates = parse_domain("omnigibson")
UNARIES = [predicate for predicate, inputs in domain_predicates.items() if len(inputs) == 1]
BINARIES = [predicate for predicate, inputs in domain_predicates.items() if len(inputs) == 2]


class TrivialBackend(BDDLBackend):
    def get_predicate_class(self, predicate_name):
        PREDICATE_MAPPING = {
            "cooked": TrivialCookedPredicate,
            "frozen": TrivialFrozenPredicate,
            "open": TrivialOpenPredicate,
            "folded": TrivialFoldedPredicate,
            "unfolded": TrivialUnfoldedPredicate,
            "toggled_on": TrivialToggledOnPredicate,
            "hot": TrivialHotPredicate,
            "frozen": TrivialFrozenPredicate,
            "on_fire": TrivialOnFirePredicate,
            "empty": TrivialEmptyPredicate,
            "closed": TrivialClosedPredicate,
            "future": TrivialFuturePredicate,
            "real": TrivialRealPredicate,
            "covered": TrivialCoveredPredicate,
            "ontop": TrivialOnTopPredicate,
            "inside": TrivialInsidePredicate,
            "filled": TrivialFilledPredicate,
            "saturated": TrivialSaturatedPredicate,
            "contains": TrivialContainsPredicate,
            "ontop": TrivialOnTopPredicate,
            "nextto": TrivialNextToPredicate,
            "under": TrivialUnderPredicate,
            "touching": TrivialTouchingPredicate,
            "overlaid": TrivialOverlaidPredicate,
            "attached": TrivialAttachedPredicate,
            "draped": TrivialDrapedPredicate,
            "insource": TrivialInsourcePredicate,
            "broken": TrivialBrokenPredicate,
            "assembled": TrivialAssembledPredicate,
            "grasped": TrivialGraspedPredicate,
        } 
        return PREDICATE_MAPPING[predicate_name]


class TrivialSimulator(object):
    def __init__(self):
        # Unaries - populated with 1-tuples of string names 
        self.cooked = set()
        self.frozen = set()
        self.open = set()
        self.folded = set()
        self.unfolded = set()
        self.toggled_on = set() 
        self.hot = set() 
        self.on_fire = set() 
        self.empty = set() 
        self.future = set() 
        self.real = set() 
        self.broken = set()
        self.closed = set()
        self.assembled = set()
        # Binaries - populated with 2-tuples of string names
        self.saturated = set()
        self.covered = set() 
        self.filled = set() 
        self.contains = set() 
        self.ontop = set() 
        self.nextto = set() 
        self.under = set() 
        self.touching = set() 
        self.inside = set() 
        self.overlaid = set() 
        self.attached = set() 
        self.draped = set() 
        self.insource = set() 
        self.grasped = set()

        self.create_predicate_to_setters()
    
    def create_predicate_to_setters(self):
        self.predicate_to_setters = {
            "cooked": self.set_cooked,
            "frozen": self.set_frozen,
            "open": self.set_open,
            "folded": self.set_folded,
            "unfolded": self.set_unfolded,
            "toggled_on": self.set_toggled_on,
            "hot": self.set_hot,
            "on_fire": self.set_on_fire,
            "empty": self.set_empty,
            "broken": self.set_broken,
            "assembled": self.set_assembled,
            "closed": self.set_closed,
            "future": self.set_future,
            "real": self.set_real,
            "inside": self.set_inside,
            "ontop": self.set_ontop,
            "covered": self.set_covered,
            "filled": self.set_filled,
            "saturated": self.set_saturated,
            "nextto": self.set_nextto,
            "contains": self.set_contains,
            "under": self.set_under,
            "touching": self.set_touching,
            "overlaid": self.set_overlaid,
            "attached": self.set_attached,
            "draped": self.set_draped,
            "insource": self.set_insource,
            "grasped": self.set_grasped,
        }

    def set_state(self, literals): 
        """
        Given a set of non-contradictory parsed ground literals, set this backend to them. 
        Also set implied predicates:
            filled => contains
            not contains => not filled 
            ontop => nextto
            not nextto => not ontop
            TODO under? others? draped?
        """
        with open(ver.PROPS_TO_SYNS_JSON, "r") as f:
            props_to_syns = json.load(f)
        with open(ver.SYNS_TO_PROPS_PARAMS_JSON, "r") as f:
            syns_to_props_params = json.load(f)
        
        # TODO maybe do this few a through times so that residual effects get a chance to fire
        for literal in literals: 
            if literal == ["covered", "french_toast.n.01_1", "maple_syrup.n.01_1"]:
                printing = True 
            else:
                printing = False

            is_predicate = not(literal[0] == "not")
            predicate, *objects = literal[1] if (literal[0] == "not") else literal
            if printing:
                print(predicate)
                print(objects)
                print("is predicate:", is_predicate)
                print()
            if predicate == "inroom": 
                # print(f"Skipping inroom literal {literal}")
                continue
            self.predicate_to_setters[predicate](tuple(objects), is_predicate)

            if printing:
                print(("french_toast.n.01_1", "maple_syrup.n.01_1") in self.covered)

            # Start by setting elements as real unless they are in a future or explicit not-real statement
            if not (is_predicate and (predicate == "future")) and not ((not is_predicate) and (predicate == "real")):
                for obj in objects:
                    self.predicate_to_setters["real"](tuple([obj]), True)

            # Entailed predicates 
            if is_predicate and (predicate == "filled"):
                self.predicate_to_setters["contains"](tuple(objects), True)
            if (not is_predicate) and (predicate == "contains"):
                self.predicate_to_setters["filled"](tuple(objects), False)
            if is_predicate and (predicate == "ontop"):
                self.predicate_to_setters["nextto"](tuple(objects), True)
                self.predicate_to_setters["touching"](tuple(objects), True)
            if is_predicate and (predicate == "inside"):
                self.predicate_to_setters["nextto"](tuple(objects), True)
            if (not is_predicate) and (predicate == "nextto"):
                self.predicate_to_setters["ontop"](tuple(objects), False)
            if is_predicate and (predicate == "nextto"):
                self.predicate_to_setters["nextto"](tuple(reversed(objects)), True)
            if (not is_predicate) and (predicate == "nextto"):
                self.predicate_to_setters["nextto"](tuple(reversed(objects)), False)
            
            if is_predicate and (predicate == "closed"):
                self.predicate_to_setters["open"](tuple(objects), False)
            if is_predicate and (predicate == "open"):
                self.predicate_to_setters["closed"](tuple(objects), False)
            if is_predicate and (predicate == "filled"):
                self.predicate_to_setters["empty"](tuple([objects[0]]), False)
            if is_predicate and (predicate == "folded"):
                self.predicate_to_setters["unfolded"](tuple(objects), False)
            if is_predicate and (predicate == "unfolded"):
                self.predicate_to_setters["folded"](tuple(objects), False)
            
            # Transitive insides/not-insides
            if predicate == "inside":
                item, item_its_inside = objects
                for test_item_inside_it, test_item in copy.deepcopy(self.inside): 
                    if test_item == item:
                        # False if item is not inside item_its_inside, True if item is inside item_its_inside
                        self.predicate_to_setters["inside"](tuple([test_item_inside_it, item_its_inside]), is_predicate)
            
            # If A is inside B and B gets filled with or contains C, A is covered in C (if types check)
            if is_predicate and (predicate in ["filled", "contains"]):
                filled_obj, filling_obj = objects
                # inside pred --> inside_obj is a nonSubstance.
                # particleRemovers can be saturated tho.
                for inside_obj, outside_obj in self.inside:
                    if outside_obj == filled_obj:
                        inside_syn = re.match(ver.OBJECT_CAT_AND_INST_RE, inside_obj).group()
                        if ("rigidBody" in syns_to_props_params[inside_syn]) or ("softBody" in syns_to_props_params[inside_syn]):
                            self.predicate_to_setters["covered"](tuple([inside_obj, filling_obj]), True)
                        if "particleRemover" in syns_to_props_params[inside_syn]:
                            self.predicate_to_setters["saturated"](tuple([inside_obj, filling_obj]), True)

            if printing:
                print("line 211", ("french_toast.n.01_1", "maple_syrup.n.01_1") in self.covered)
            
            if is_predicate and (predicate == "inside"):
                inside_obj, outside_obj = objects 
                for filled_obj, filling_obj in self.filled.union(self.contains):
                    if outside_obj == filled_obj:
                        inside_syn = re.match(ver.OBJECT_CAT_AND_INST_RE, inside_obj).group()
                        if ("rigidBody" in syns_to_props_params[inside_syn]) or ("softBody" in syns_to_props_params[inside_syn]):
                            self.predicate_to_setters["covered"](tuple([inside_obj, filling_obj]), True)
                        if "particleRemover" in syns_to_props_params[inside_syn]:
                            self.predicate_to_setters["saturated"](tuple([inside_obj, filling_obj]), True)

            # Empty --> not filled with anything
            if is_predicate and (predicate == "empty"):
                empty_obj = objects[0]
                for filled_obj1, filled_obj2 in copy.deepcopy(self.filled):
                    if filled_obj1 == empty_obj:
                        self.filled.discard((filled_obj1, filled_obj2))
                for contains_obj1, contains_obj2 in copy.deepcopy(self.contains):
                    if contains_obj1 == empty_obj:
                        self.contains.discard((contains_obj1, contains_obj2))

            if printing:
                print("line 234", ("french_toast.n.01_1", "maple_syrup.n.01_1") in self.covered)

            # Thermal effects
            # If we encounter a hot vessel and a cookable inside it...
            if is_predicate and (predicate == "hot"): 
                # Any cookable ontop, inside, filled, contained, or covered gets cooked; any meltable accordingly gets melted.
                # If both - melting happens first. 
                for ontop_obj1, ontop_obj2 in copy.deepcopy(self.ontop): 
                    ontop_syn1 = re.match(ver.OBJECT_CAT_AND_INST_RE, ontop_obj1).group()
                    if (ontop_obj2 == objects[0]) and (ontop_syn1 in props_to_syns["meltable"]):
                        meltable_derivative_obj1 = syns_to_props_params[ontop_syn1]["meltable"]["meltable_derivative_synset"] + "_1"
                        self.predicate_to_setters["real"](tuple([meltable_derivative_obj1]), True)
                        self.predicate_to_setters["real"](tuple([ontop_obj1]), False)
                        self.predicate_to_setters["contains"](tuple([ontop_obj2, meltable_derivative_obj1]), True)
                        self.predicate_to_setters["ontop"](tuple([ontop_obj1, ontop_obj2]), False)
                    elif (ontop_obj2 == objects[0]) and (ontop_syn1 in props_to_syns["cookable"]):
                        self.predicate_to_setters["cooked"](tuple([ontop_obj1]), True)
                for inside_obj1, inside_obj2 in copy.deepcopy(self.inside): 
                    inside_syn1 = re.match(ver.OBJECT_CAT_AND_INST_RE, inside_obj1).group()
                    if (inside_obj2 == objects[0]) and (inside_syn1 in props_to_syns["meltable"]):
                        meltable_derivative_obj1 = syns_to_props_params[inside_syn1]["meltable"]["meltable_derivative_synset"] + "_1"
                        self.predicate_to_setters["real"](tuple([meltable_derivative_obj1]), True)
                        self.predicate_to_setters["real"](tuple([inside_obj1]), False)
                        self.predicate_to_setters["contains"](tuple([inside_obj2, meltable_derivative_obj1]), True)
                        self.predicate_to_setters["inside"](tuple([inside_obj1, inside_obj2]), False)
                    if (inside_obj2 == objects[0]) and (inside_syn1 in props_to_syns["cookable"]):
                        self.predicate_to_setters["cooked"](tuple([inside_obj1]), True)
                for filled_obj1, filled_obj2 in self.filled:
                    filled_syn2 = re.match(ver.OBJECT_CAT_AND_INST_RE, filled_obj2).group()
                    if (filled_obj1 == objects[0]) and (filled_syn2 in props_to_syns["cookable"]):
                        self.predicate_to_setters["real"](tuple([filled_obj2]), False)
                        cooking_derivative_obj2 = syns_to_props_params[filled_syn2]["cookable"]["substance_cooking_derivative_synset"] + "_1"
                        self.predicate_to_setters["real"](tuple([cooking_derivative_obj2]), True)
                        self.predicate_to_setters["filled"](tuple([filled_obj1, cooking_derivative_obj2]), True)
                        self.predicate_to_setters["filled"](tuple([filled_obj1, filled_obj2]), False)
                        self.predicate_to_setters["contains"](tuple([filled_obj1, cooking_derivative_obj2]), True)
                        self.predicate_to_setters["contains"](tuple([filled_obj1, filled_obj2]), False)
                for contained_obj1, contained_obj2 in self.contains:
                    contained_syn2 = re.match(ver.OBJECT_CAT_AND_INST_RE, contained_obj2).group()
                    if (contained_obj1 == objects[0]) and (contained_syn2 in props_to_syns["cookable"]):
                        self.predicate_to_setters["real"](tuple([contained_obj2]), False)
                        cooking_derivative_obj2 = syns_to_props_params[contained_syn2]["cookable"]["substance_cooking_derivative_synset"] + "_1"
                        self.predicate_to_setters["real"](tuple([cooking_derivative_obj2]), True)
                        self.predicate_to_setters["contains"](tuple([contained_obj1, cooking_derivative_obj2]), True)
                        self.predicate_to_setters["contains"](tuple([contained_obj1, contained_obj2]), False)

            if printing:
                print("line 281", ("french_toast.n.01_1", "maple_syrup.n.01_1") in self.covered)
            
            # If we encounter a nonSubstance touching or nextto a toggled_on heatsource, it should get hot and unfrozen
            if is_predicate and (predicate in ["touching", "nextto", "ontop", "inside", "overlaid", "draped"]):
                syn0 = re.match(ver.OBJECT_CAT_AND_INST_RE, objects[0]).group()
                syn1 = re.match(ver.OBJECT_CAT_AND_INST_RE, objects[1]).group()
                if (syn0 not in props_to_syns["substance"]) and (syn1 in props_to_syns["heatSource"]):
                    heatsource_params = syns_to_props_params[syn1]["heatSource"]
                    # Check heat source requirements
                    toggled_on_ok = (heatsource_params["requires_toggled_on"] == 0.) or ((heatsource_params["requires_toggled_on"] == 1.) and (tuple([objects[1]]) in self.toggled_on))
                    closed_ok = (heatsource_params["requires_closed"] == 0.) or ((heatsource_params["requires_toggled_on"] == 1.) and ((tuple([objects[1]]) not in self.open) or (tuple([objects[1]]) in self.closed)))
                    inside_ok = (heatsource_params["requires_inside"] == 0.) or ((heatsource_params["requires_inside"] == 1.) and (tuple(objects) in self.inside))
                    if toggled_on_ok and closed_ok and inside_ok: 
                        self.predicate_to_setters["frozen"](tuple([objects[0]]), False)
                        self.predicate_to_setters["hot"](tuple([objects[0]]), True)
            
            # Freezing for electric refrigerator
            if (not is_predicate) and (predicate == "open"):
                for inside_obj0, inside_obj1 in self.inside:
                    inside_syn0 = re.match(ver.OBJECT_CAT_AND_INST_RE, inside_obj0).group()
                    inside_syn1 = re.match(ver.OBJECT_CAT_AND_INST_RE, inside_obj1).group()
                    if inside_syn1 == "electric_refrigerator.n.01":
                        # We know the fridge is closed since that's when this is triggered, the object is inside it since that's what we're looking at, and toggled_on isn't a requirement
                        self.predicate_to_setters["frozen"](tuple([inside_obj0]), True)
            
            # TODO need to flip for when the heatsource engages second (RIPPPPP, maybe just rely on explicitly claiming the thing is getting hot)

            if printing:
                print("line 309", ("french_toast.n.01_1", "maple_syrup.n.01_1") in self.covered)
                from pprint import pprint
                pprint(self.covered)

            # If we encounter a potential cooking placement of a cookable relative to a hot vessel...
            if is_predicate and (predicate in ["ontop", "inside"]):
                syn0 = re.match(ver.OBJECT_CAT_AND_INST_RE, objects[0]).group()
                if (syn0 in props_to_syns["cookable"]) and (tuple([objects[1]]) in self.hot):
                    self.predicate_to_setters["cooked"](tuple([objects[0]]), True)
            if is_predicate and (predicate in ["filled", "contains", "covered"]):
                syn1 = re.match(ver.OBJECT_CAT_AND_INST_RE, objects[1]).group()
                if (syn1 in props_to_syns["cookable"] and (tuple([objects[0]])) in self.hot):
                    cookable_derivative = syns_to_props_params[syn1]["cookable"]["substance_cooking_derivative_synset"] + "_1"
                    self.predicate_to_setters["real"](tuple([cookable_derivative]), True)
                    self.predicate_to_setters[predicate](tuple([objects[0], cookable_derivative]), True)
                    self.predicate_to_setters[predicate](tuple(objects), False)

            if printing:
                print("line 322", ("french_toast.n.01_1", "maple_syrup.n.01_1") in self.covered)
                from pprint import pprint
                pprint(self.covered)

            # If we encounter a potential melting placement of a meltable relative to a hot vessel...
            if is_predicate and (predicate in ["inside", "ontop"]):
                syn0 = re.match(ver.OBJECT_CAT_AND_INST_RE, objects[0]).group()
                if (syn0 in props_to_syns["meltable"]) and (tuple([objects[1]]) in self.hot):
                    meltable_derivative = syns_to_props_params[syn0]["meltable"]["meltable_derivative_synset"] + "_1"
                    self.predicate_to_setters["real"](tuple([meltable_derivative]), True)
                    self.predicate_to_setters["real"](tuple([objects[0]]), False)
                    self.predicate_to_setters["contains"](tuple([objects[1], meltable_derivative]), True)
                    self.predicate_to_setters[predicate](tuple(objects), False)

            if printing:
                print("line 332", ("french_toast.n.01_1", "maple_syrup.n.01_1") in self.covered)

            # Washer-dryer
            if is_predicate and (predicate == "toggled_on") and ("washer.n.03" in objects[0]):
                for inside_obj0, inside_obj1 in self.inside:
                    if "washer.n.03" not in inside_obj1:
                        continue
                    inside_syn0, inside_syn1 = re.match(ver.OBJECT_CAT_AND_INST_RE, inside_obj0).group(), re.match(ver.OBJECT_CAT_AND_INST_RE, inside_obj1).group()
                    # Water on
                    self.predicate_to_setters["covered"](tuple([inside_obj0, "water.n.06_1"]), True)
                    if "particleRemover" in syns_to_props_params[inside_syn0]:
                        self.predicate_to_setters["saturated"](tuple([inside_obj0, "water.n.06_1"]), True)
                    
                    # Stain off based on what else is in there
                    for covered_obj, covering_obj in copy.deepcopy(self.covered):
                        covered_syn, covering_syn = re.match(ver.OBJECT_CAT_AND_INST_RE, covered_obj).group(), re.match(ver.OBJECT_CAT_AND_INST_RE, covering_obj).group()
                        conditions = syns_to_props_params["rag.n.01"]["particleRemover"]["conditions"]
                        spec_conditions = conditions[covering_syn]
                        can_clean = False
                        if not spec_conditions: 
                            can_clean = True
                        for __, cleansing_syn in spec_conditions:
                            if (tuple([inside_obj1, cleansing_syn + "_1"]) in self.contains) or (tuple([inside_obj1, cleansing_syn + "_1"]) in self.filled):
                                self.predicate_to_setters["covered"](tuple([covered_obj, covering_obj]), False)
                                if "particleRemover" in syns_to_props_params[covered_syn]:
                                    self.predicate_to_setters["saturated"](tuple([covered_obj, covering_obj]), False)
            
            if is_predicate and (predicate == "toggled_on") and ("clothes_dryer.n.01" in objects[0]):
                for inside_obj0, inside_obj1 in self.inside:
                    inside_syn0, inside_syn1 = re.match(ver.OBJECT_CAT_AND_INST_RE, inside_obj0).group(), re.match(ver.OBJECT_CAT_AND_INST_RE, inside_obj1).group()
                    self.predicate_to_setters["covered"](tuple([inside_obj0, "water.n.06_1"]), False)
                    if "particleRemover" in syns_to_props_params[inside_syn0]:
                        self.predicate_to_setters["saturated"](tuple([inside_obj0, "water.n.06_1"]), False)

            # TODO coldSource

            # TODO when a new object is created, its positional predicates are the same with the same objects as the original 
            
            # TODO slicing and dicing effects
            if is_predicate and (predicate == "touching"):
                syn0, syn1 = re.match(ver.OBJECT_CAT_AND_INST_RE, objects[0]).group(), re.match(ver.OBJECT_CAT_AND_INST_RE, objects[1]).group() 
                if "slicer" in syns_to_props_params[syn0]:
                    if "sliceable" in syns_to_props_params[syn1]:
                        sliced_synset = syns_to_props_params[syn1]["sliceable"]["sliceable_derivative_synset"]
                        existing_sliceds = set([obj for obj in self.real if sliced_synset in obj])
                        existing_indices = [int(existing_sliced.split("_")[0]) for existing_sliced in existing_sliceds]
                        if existing_indices:
                            new_index1 = max(existing_indices) + 1
                        else:
                            new_index1 = 1
                        new_index2 = new_index1 + 1
                        self.predicate_to_setters["real"](tuple([objects[1]]), False)
                        self.predicate_to_setters["real"](tuple([f"{sliced_synset}_{new_index1}"]), True)
                        self.predicate_to_setters["real"](tuple([f"{sliced_synset}_{new_index2}"]), True)
                    elif "diceable" in syns_to_props_params[syn1]:
                        if syn1 in self.cooked:
                            diced_synset = syns_to_props_params[syn1]["diceable"]["cooked_diceable_derivative_synset"]
                        else:
                            diced_synset = syns_to_props_params[syn1]["diceable"]["uncooked_diceable_derivative_synset"]
                        self.predicate_to_setters["real"](tuple([objects[1]]), False)
                        self.predicate_to_setters["real"](tuple([f"{diced_synset}_1"]), True)
                elif "slicer" in syns_to_props_params[syn1]:
                    if "sliceable" in syns_to_props_params[syn0]:
                        sliced_synset = syns_to_props_params[syn0]["sliceable"]["sliceable_derivative_synset"]
                        existing_sliceds = set([obj for obj in self.real if sliced_synset in obj])
                        existing_indices = [int(existing_sliced.split("_")[0]) for existing_sliced in existing_sliceds]
                        if existing_indices:
                            new_index1 = max(existing_indices) + 1
                        else:
                            new_index1 = 1
                        new_index2 = new_index1 + 1
                        self.predicate_to_setters["real"](tuple([objects[0]]), False)
                        self.predicate_to_setters["real"](tuple([f"{sliced_synset}_{new_index1}"]), True)
                        self.predicate_to_setters["real"](tuple([f"{sliced_synset}_{new_index2}"]), True)
                    elif "diceable" in syns_to_props_params[syn0]:
                        if syn0 in self.cooked:
                            diced_synset = syns_to_props_params[syn0]["diceable"]["cooked_diceable_derivative_synset"]
                        else:
                            diced_synset = syns_to_props_params[syn0]["diceable"]["uncooked_diceable_derivative_synset"]
                        self.predicate_to_setters["real"](tuple([objects[0]]), False)
                        self.predicate_to_setters["real"](tuple([f"{diced_synset}_1"]), True)

            # TODO transition recipes
            if printing:
                print(("french_toast.n.01_1", "maple_syrup.n.01_1") in self.covered)
            
            # from pprint import pprint;
            # pprint(self.covered)
        
    def set_cooked(self, objs, is_cooked):
        assert len(objs) == 1, f"`objs` has len other than 1: {objs}"
        if is_cooked:  
            self.cooked.add(objs)
        else: 
            self.cooked.discard(objs)
    
    def get_cooked(self, objs):
        return tuple(obj.name for obj in objs) in self.cooked
    
    def set_frozen(self, objs, is_frozen):
        assert len(objs) == 1, f"`objs` has len other than 1: {objs}"
        if is_frozen: 
            self.frozen.add(objs)
        else: 
            self.frozen.discard(objs)
    
    def get_frozen(self, objs):
        return tuple(obj.name for obj in objs) in self.frozen
    
    def set_open(self, objs, is_open):
        assert len(objs) == 1, f"`objs` has len other than 1: {objs}"
        if is_open: 
            self.open.add(objs)
        else: 
            self.open.discard(objs)
    
    def get_open(self, objs):
        return tuple(obj.name for obj in objs) in self.open
    
    def set_folded(self, objs, is_folded):
        assert len(objs) == 1, f"`objs` has len other than 1: {objs}"
        if is_folded: 
            self.folded.add(objs)
        else: 
            self.folded.discard(objs)
    
    def get_folded(self, objs):
        return tuple(obj.name for obj in objs) in self.folded
    
    def set_unfolded(self, objs, is_unfolded):
        assert len(objs) == 1, f"`objs` has len other than 1: {objs}"
        if is_unfolded: 
            self.unfolded.add(objs)
        else: 
            self.unfolded.discard(objs)
    
    def get_unfolded(self, objs):
        return tuple(obj.name for obj in objs) in self.unfolded
    
    def set_toggled_on(self, objs, is_toggled_on):
        assert len(objs) == 1, f"`objs` has len other than 1: {objs}"
        if is_toggled_on: 
            self.toggled_on.add(objs)
        else: 
            self.toggled_on.discard(objs)
    
    def get_toggled_on(self, objs):
        return tuple(obj.name for obj in objs) in self.toggled_on
    
    def set_hot(self, objs, is_hot):
        assert len(objs) == 1, f"`objs` has len other than 1: {objs}"
        if is_hot: 
            self.hot.add(objs)
        else: 
            self.hot.discard(objs)
    
    def get_hot(self, objs):
        return tuple(obj.name for obj in objs) in self.hot
    
    def set_on_fire(self, objs, is_on_fire):
        assert len(objs) == 1, f"`objs` has len other than 1: {objs}"
        if is_on_fire: 
            self.on_fire.add(objs)
        else: 
            self.on_fire.discard(objs)
    
    def get_on_fire(self, objs):
        return tuple(obj.name for obj in objs) in self.on_fire
    
    def set_empty(self, objs, is_empty):
        assert len(objs) == 1, f"`objs` has len other than 1: {objs}"
        if is_empty: 
            self.empty.add(objs)
        else: 
            self.empty.discard(objs)
    
    def get_empty(self, objs):
        return tuple(obj.name for obj in objs) in self.empty
    
    def set_closed(self, objs, is_closed):
        assert len(objs) == 1, f"`objs` has len other than 1: {objs}"
        if is_closed: 
            self.closed.add(objs)
        else: 
            self.closed.discard(objs)
    
    def get_closed(self, objs):
        return tuple(obj.name for obj in objs) in self.closed
    
    def set_broken(self, objs, is_broken):
        assert len(objs) == 1, f"`objs` has len other than 1: {objs}"
        if is_broken: 
            self.broken.add(objs)
        else: 
            self.broken.discard(objs)
    
    def get_broken(self, objs):
        return tuple(obj.name for obj in objs) in self.broken
    
    def set_assembled(self, objs, is_assembled):
        assert len(objs) == 1, f"`objs` has len other than 1: {objs}"
        if is_assembled: 
            self.assembled.add(objs)
        else: 
            self.assembled.discard(objs)
    
    def get_assembled(self, objs):
        return tuple(obj.name for obj in objs) in self.assembled
    
    def set_future(self, objs, is_future):
        assert len(objs) == 1, f"`objs` has len other than 1: {objs}"
        if is_future: 
            self.future.add(objs)
        else: 
            self.future.discard(objs)
    
    def get_future(self, objs):
        return tuple(obj.name for obj in objs) in self.future
    
    def set_real(self, objs, is_real):
        assert len(objs) == 1, f"`objs` has len other than 1: {objs}"
        if is_real: 
            self.real.add(objs)
        else: 
            self.real.discard(objs)
    
    def get_real(self, objs):
        return tuple(obj.name for obj in objs) in self.real

    def set_covered(self, objs, is_covered):
        assert len(objs) == 2, f"`objs` has length other than 2: {objs}"
        if is_covered:
            self.covered.add(objs)
        else:
            self.covered.discard(objs)

    def get_covered(self, objs):
        return tuple(obj.name for obj in objs) in self.covered
    
    def set_ontop(self, objs, is_ontop):
        assert len(objs) == 2, f"`objs` has length other than 2: {objs}"
        if is_ontop:
            self.ontop.add(objs)
        else:
            self.ontop.discard(objs)

    def get_ontop(self, objs):
        return tuple(obj.name for obj in objs) in self.ontop
    
    def set_inside(self, objs, is_inside):
        assert len(objs) == 2, f"`objs` has length other than 2: {objs}"
        if is_inside:
            self.inside.add(objs)
        else:
            self.inside.discard(objs)
    
    def get_inside(self, objs):
        return tuple(obj.name for obj in objs) in self.inside
    
    def set_filled(self, objs, is_filled):
        assert len(objs) == 2, f"`objs` has length other than 2: {objs}"
        if is_filled:
            self.filled.add(objs)
        else:
            self.filled.discard(objs)
    
    def get_filled(self, objs):
        return tuple(obj.name for obj in objs) in self.filled

    def set_saturated(self, objs, is_saturated):
        assert len(objs) == 2, f"`objs` has length other than 2: {objs}"
        if is_saturated:
            self.saturated.add(objs)
        else:
            self.saturated.discard(objs)
    
    def get_saturated(self, objs):
        return tuple(obj.name for obj in objs) in self.saturated

    def set_nextto(self, objs, is_nextto):
        assert len(objs) == 2, f"`objs` has length other than 2: {objs}"
        if is_nextto:
            self.nextto.add(objs)
        else:
            self.nextto.discard(objs)
    
    def get_nextto(self, objs):
        return tuple(obj.name for obj in objs) in self.nextto

    def set_contains(self, objs, is_contains):
        assert len(objs) == 2, f"`objs` has length other than 2: {objs}"
        if is_contains:
            self.contains.add(objs)
        else:
            self.contains.discard(objs)
    
    def get_contains(self, objs):
        return tuple(obj.name for obj in objs) in self.contains
    
    def set_under(self, objs, is_under):
        assert len(objs) == 2, f"`objs` has length other than 2: {objs}"
        if is_under:
            self.under.add(objs)
        else:
            self.under.discard(objs)
    
    def get_under(self, objs):
        return tuple(obj.name for obj in objs) in self.under

    def set_touching(self, objs, is_touching):
        assert len(objs) == 2, f"`objs` has length other than 2: {objs}"
        if is_touching:
            self.touching.add(objs)
        else:
            self.touching.discard(objs)
    
    def get_touching(self, objs):
        return tuple(obj.name for obj in objs) in self.touching
    
    def set_overlaid(self, objs, is_overlaid):
        assert len(objs) == 2, f"`objs` has length other than 2: {objs}"
        if is_overlaid:
            self.overlaid.add(objs)
        else:
            self.overlaid.discard(objs)
    
    def get_overlaid(self, objs):
        return tuple(obj.name for obj in objs) in self.overlaid
    
    def set_attached(self, objs, is_attached):
        assert len(objs) == 2, f"`objs` has length other than 2: {objs}"
        if is_attached:
            self.attached.add(objs)
        else:
            self.attached.discard(objs)
    
    def get_attached(self, objs):
        return tuple(obj.name for obj in objs) in self.attached

    def set_draped(self, objs, is_draped):
        assert len(objs) == 2, f"`objs` has length other than 2: {objs}"
        if is_draped:
            self.draped.add(objs)
        else:
            self.draped.discard(objs)
    
    def get_draped(self, objs):
        return tuple(obj.name for obj in objs) in self.draped
    
    def set_insource(self, objs, is_insource):
        assert len(objs) == 2, f"`objs` has length other than 2: {objs}"
        if is_insource:
            self.insource.add(objs)
        else:
            self.insource.discard(objs)
    
    def get_insource(self, objs):
        return tuple(obj.name for obj in objs) in self.insource
    
    def set_grasped(self, objs, is_grasped):
        assert len(objs) == 2, f"`objs` has length other than 2: {objs}"
        if is_grasped:
            self.grasped.add(objs)
        else:
            self.grasped.discard(objs)
    
    def get_grasped(self, objs):
        return tuple(obj.name for obj in objs) in self.grasped


class TrivialGenericObject(object): 
    def __init__(self, name, simulator):
        self.name = name
        self.simulator = simulator
    
    def get_cooked(self):
        return self.simulator.get_cooked((self,))
    
    def get_frozen(self):
        return self.simulator.get_frozen((self,))
    
    def get_open(self):
        return self.simulator.get_open((self,))
    
    def get_folded(self):
        return self.simulator.get_folded((self,))
    
    def get_unfolded(self):
        return self.simulator.get_unfolded((self,))
    
    def get_toggled_on(self):
        return self.simulator.get_toggled_on((self,))
    
    def get_closed(self):
        return self.simulator.get_closed((self,))
    
    def get_hot(self):
        return self.simulator.get_hot((self,))
    
    def get_on_fire(self):
        return self.simulator.get_on_fire((self,))
    
    def get_empty(self):
        return self.simulator.get_empty((self,))
    
    def get_broken(self):
        return self.simulator.get_broken((self,))
    
    def get_assembled(self):
        return self.simulator.get_assembled((self,))
    
    def get_future(self):
        return self.simulator.get_future((self,))
    
    def get_real(self):
        return self.simulator.get_real((self,))
    
    def get_ontop(self, other):
        return self.simulator.get_ontop((self, other))
    
    def get_filled(self, other):
        return self.simulator.get_filled((self, other))
    
    def get_covered(self, other):
        return self.simulator.get_covered((self, other))

    def get_inside(self, other):
        return self.simulator.get_inside((self, other))
    
    def get_saturated(self, other):
        return self.simulator.get_saturated((self, other))

    def get_nextto(self, other):
        return self.simulator.get_nextto((self, other))

    def get_contains(self, other):
        return self.simulator.get_contains((self, other))

    def get_under(self, other):
        return self.simulator.get_under((self, other))

    def get_touching(self, other):
        return self.simulator.get_touching((self, other))

    def get_overlaid(self, other):
        return self.simulator.get_overlaid((self, other))

    def get_attached(self, other):
        return self.simulator.get_attached((self, other))

    def get_draped(self, other):
        return self.simulator.get_draped((self, other))

    def get_insource(self, other):
        return self.simulator.get_insource((self, other))
    
    def get_grasped(self, other):
        return self.simulator.get_grasped((self, other))


# OmniGibson trivial predicates
class TrivialCookedPredicate(UnaryAtomicFormula):
    STATE_NAME = "cooked"

    def _evaluate(self, obj):
        # print(self.STATE_NAME, obj.name, obj.get_cooked())
        return obj.get_cooked()

    def _sample(self, obj1, binary_state):
        pass


class TrivialFrozenPredicate(UnaryAtomicFormula):
    STATE_NAME = "frozen"

    def _evaluate(self, obj):
        # print(self.STATE_NAME, obj.name, obj.get_frozen())
        return obj.get_frozen()

    def _sample(self, obj1, binary_state):
        pass


class TrivialOpenPredicate(UnaryAtomicFormula):
    STATE_NAME = "open"

    def _evaluate(self, obj):
        # print(self.STATE_NAME, obj.name, obj.get_open())
        return obj.get_open()

    def _sample(self, obj1, binary_state):
        pass


class TrivialFoldedPredicate(UnaryAtomicFormula):
    STATE_NAME = "folded"

    def _evaluate(self, obj):
        # print(self.STATE_NAME, obj.name, obj.get_folded())
        return obj.get_folded()

    def _sample(self, obj1, binary_state):
        pass


class TrivialUnfoldedPredicate(UnaryAtomicFormula):
    STATE_NAME = "unfolded"

    def _evaluate(self, obj):
        # print(self.STATE_NAME, obj.name, obj.get_unfolded())
        return obj.get_unfolded()

    def _sample(self, obj1, binary_state):
        pass


class TrivialToggledOnPredicate(UnaryAtomicFormula):
    STATE_NAME = "toggled_on"

    def _evaluate(self, obj):
        # print(self.STATE_NAME, obj.name, obj.get_toggled_on())
        return obj.get_toggled_on()

    def _sample(self, obj1, binary_state):
        pass


class TrivialClosedPredicate(UnaryAtomicFormula):
    STATE_NAME = "closed"

    def _evaluate(self, obj):
        # print(self.STATE_NAME, obj.name, obj.get_closed())
        return obj.get_closed()

    def _sample(self, obj1, binary_state):
        pass


class TrivialOnFirePredicate(UnaryAtomicFormula):
    STATE_NAME = "on_fire"

    def _evaluate(self, obj):
        # print(self.STATE_NAME, obj.name, obj.get_on_fire())
        return obj.get_on_fire()

    def _sample(self, obj1, binary_state):
        pass


class TrivialHotPredicate(UnaryAtomicFormula):
    STATE_NAME = "hot"

    def _evaluate(self, obj):
        # print(self.STATE_NAME, obj.name, obj.get_hot())
        return obj.get_hot()

    def _sample(self, obj1, binary_state):
        pass


class TrivialEmptyPredicate(UnaryAtomicFormula):
    STATE_NAME = "empty"

    def _evaluate(self, obj):
        # print(self.STATE_NAME, obj.name, obj.get_empty())
        return obj.get_empty()

    def _sample(self, obj1, binary_state):
        pass


class TrivialBrokenPredicate(UnaryAtomicFormula):
    STATE_NAME = "broken"

    def _evaluate(self, obj):
        # print(self.STATE_NAME, obj.name, obj.get_broken())
        return obj.get_broken()

    def _sample(self, obj1, binary_state):
        pass


class TrivialAssembledPredicate(UnaryAtomicFormula):
    STATE_NAME = "assembled"

    def _evaluate(self, obj):
        # print(self.STATE_NAME, obj.name, obj.get_assembled())
        return obj.get_assembled()

    def _sample(self, obj1, binary_state):
        pass


class TrivialFuturePredicate(UnaryAtomicFormula):
    STATE_NAME = "future"

    def _evaluate(self, obj):
        # print(self.STATE_NAME, obj.name, obj.get_future())
        return obj.get_future()

    def _sample(self, obj1, binary_state):
        pass


class TrivialRealPredicate(UnaryAtomicFormula):
    STATE_NAME = "real"

    def _evaluate(self, obj):
        # print(self.STATE_NAME, obj.name, obj.get_real())
        return obj.get_real()

    def _sample(self, obj1, binary_state):
        pass


class TrivialCoveredPredicate(BinaryAtomicFormula):
    STATE_NAME = "covered"

    def _evaluate(self, obj1, obj2):
        # print(self.STATE_NAME, obj1.name, obj2.name, obj1.get_covered(obj2))
        return obj1.get_covered(obj2)

    def _sample(self, obj1, obj2, binary_state):
        pass


class TrivialInsidePredicate(BinaryAtomicFormula):
    STATE_NAME = "inside"

    def _evaluate(self, obj1, obj2):
        # print(self.STATE_NAME, obj1.name, obj2.name, obj1.get_inside(obj2))
        return obj1.get_inside(obj2)

    def _sample(self, obj1, obj2, binary_state):
        pass


class TrivialOnTopPredicate(BinaryAtomicFormula):
    STATE_NAME = "ontop"

    def _evaluate(self, obj1, obj2):
        return obj1.get_ontop(obj2)

    def _sample(self, obj1, obj2, binary_state):
        pass


class TrivialFilledPredicate(BinaryAtomicFormula):
    STATE_NAME = "filled"

    def _evaluate(self, obj1, obj2):
        return obj1.get_filled(obj2)

    def _sample(self, obj1, obj2, binary_state):
        pass


class TrivialSaturatedPredicate(BinaryAtomicFormula):
    STATE_NAME = "saturated"

    def _evaluate(self, obj1, obj2):
        # print(self.STATE_NAME, obj1.name, obj2.name, obj1.get_saturated(obj2))
        return obj1.get_saturated(obj2)

    def _sample(self, obj1, obj2, binary_state):
        pass


class TrivialNextToPredicate(BinaryAtomicFormula):
    STATE_NAME = "nextto"

    def _evaluate(self, obj1, obj2):
        # print(self.STATE_NAME, obj1.name, obj2.name, obj1.get_nextto(obj2))
        return obj1.get_nextto(obj2)

    def _sample(self, obj1, obj2, binary_state):
        pass


class TrivialContainsPredicate(BinaryAtomicFormula):
    STATE_NAME = "contains"

    def _evaluate(self, obj1, obj2):
        # print(self.STATE_NAME, obj1.name, obj2.name, obj1.get_contains(obj2))
        return obj1.get_contains(obj2)

    def _sample(self, obj1, obj2, binary_state):
        pass


class TrivialUnderPredicate(BinaryAtomicFormula):
    STATE_NAME = "under"

    def _evaluate(self, obj1, obj2):
        # print(self.STATE_NAME, obj1.name, obj2.name, obj1.get_under(obj2))
        return obj1.get_under(obj2)

    def _sample(self, obj1, obj2, binary_state):
        pass


class TrivialTouchingPredicate(BinaryAtomicFormula):
    STATE_NAME = "touching"

    def _evaluate(self, obj1, obj2):
        # print(self.STATE_NAME, obj1.name, obj2.name, obj1.get_touching(obj2))
        return obj1.get_touching(obj2)

    def _sample(self, obj1, obj2, binary_state):
        pass


class TrivialOverlaidPredicate(BinaryAtomicFormula):
    STATE_NAME = "overlaid"

    def _evaluate(self, obj1, obj2):
        # print(self.STATE_NAME, obj1.name, obj2.name, obj1.get_overlaid(obj2))
        return obj1.get_overlaid(obj2)

    def _sample(self, obj1, obj2, binary_state):
        pass


class TrivialAttachedPredicate(BinaryAtomicFormula):
    STATE_NAME = "attached"

    def _evaluate(self, obj1, obj2):
        # print(self.STATE_NAME, obj1.name, obj2.name, obj1.get_attached(obj2))
        return obj1.get_attached(obj2)

    def _sample(self, obj1, obj2, binary_state):
        pass


class TrivialDrapedPredicate(BinaryAtomicFormula):
    STATE_NAME = "draped"

    def _evaluate(self, obj1, obj2):
        # print(self.STATE_NAME, obj1.name, obj2.name, obj1.get_draped(obj2))
        return obj1.get_draped(obj2)

    def _sample(self, obj1, obj2, binary_state):
        pass


class TrivialInsourcePredicate(BinaryAtomicFormula):
    STATE_NAME = "insource"

    def _evaluate(self, obj1, obj2):
        # print(self.STATE_NAME, obj1.name, obj2.name, obj1.get_insource(obj2))
        return obj1.get_insource(obj2)

    def _sample(self, obj1, obj2, binary_state):
        pass


class TrivialGraspedPredicate(BinaryAtomicFormula):
    STATE_NAME = "grasped"

    def _evaluate(self, obj1, obj2):
        # print(self.STATE_NAME, obj1.name, obj2.name, obj1.get_grasped(obj2))
        return obj1.get_grasped(obj2)

    def _sample(self, obj1, obj2, binary_state):
        pass


VALID_ATTACHMENTS = set([
    ("mixing_bowl.n.01", "electric_mixer.n.01"),
    ("cork.n.04", "wine_bottle.n.01"),
    ("menu.n.01", "wall.n.01"),
    ("broken__light_bulb.n.01", "table_lamp.n.01"),
    ("light_bulb.n.01", "table_lamp.n.01"),
    ("lens.n.01", "digital_camera.n.01"),
    ("screen.n.01", "wall.n.01"),
    ("antler.n.01", "wall.n.01"),
    ("skateboard_wheel.n.01", "skateboard.n.01"),
    ("blackberry.n.01", "scrub.n.01"),
    ("raspberry.n.02", "scrub.n.01"),
    ("dip.n.07", "candlestick.n.01"),
    ("sign.n.02", "wall.n.01"),
    ("wreath.n.01", "wall.n.01"),
    ("bow.n.08", "wall.n.01"),
    ("holly.n.03", "wall.n.01"),
    ("curtain_rod.n.01", "wall.n.01"),
    ("bicycle.n.01", "bicycle_rack.n.01"),
    ("bicycle_rack.n.01", "wall.n.01"),
    ("dartboard.n.01", "wall.n.01"),
    ("rug.n.01", "wall.n.01"),
    ("fairy_light.n.01", "wall.n.01"),
    ("lantern.n.01", "wall.n.01"),
    ("address.n.05", "wall.n.01"),
    ("hanger.n.02", "wardrobe.n.01"),
    ("flagpole.n.02", "wall.n.01"),
    ("picture_frame.n.01", "wall.n.01"),
    ("wind_chime.n.01", "pole.n.01"),
    ("pole.n.01", "wall.n.01"),
    ("hook.n.05", "trailer_truck.n.01"),
    ("fire_alarm.n.02", "wall.n.01"),
    ("poster.n.01", "wall.n.01"),
    ("painting.n.01", "wall.n.01"),
    ("hanger.n.02", "coatrack.n.01"),
    ("license_plate.n.01", "car.n.01"),
    ("gummed_label.n.01", "license_plate.n.01"),
    ("wallpaper.n.01", "wall.n.01"),
    ("mirror.n.01", "wall.n.01"),
    ("webcam.n.02", "desktop_computer.n.01"),
    ("kayak.n.01", "kayak_rack.n.01"),
    ("kayak_rack.n.01", "wall.n.01"),
    ("fish.n.02", "fishing_rod.n.01"),
    ("bicycle_rack.n.01", "recreational_vehicle.n.01"),
])

VALID_ROOMS = set()