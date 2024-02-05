from ontolearn.knowledge_base import KnowledgeBase
from owlapy.model import OWLObjectProperty, OWLObjectPropertyAssertionAxiom, \
    OWLClassAssertionAxiom, IRI, OWLObjectSomeValuesFrom, OWLObjectUnionOf, \
    OWLObjectIntersectionOf, OWLClass, OWLObjectComplementOf, \
    OWLObjectAllValuesFrom, OWLNamedIndividual
from owlapy.owlready2._base import OWLReasoner_Owlready2, \
    OWLOntologyManager_Owlready2
from owlapy.owlready2.complex_ce_instances import OWLReasoner_Owlready2_ComplexCEInstances
from collections import OrderedDict
from owlapy.util import NNF, TopLevelCNF, TopLevelDNF
import os

'''
This is an implementation of the counterfactual KB algorithm from the paper "Counterfactual Explanations for
Classifiers Using the Description Logic ALCH" (to be published).

Given a knowledge base and a concept CC in ALCH and an individual in that KB, 
we create counterfactuals of this KB where K does not model CC(x).
'''

class CounterfactualCandidateGenerator:
    '''
    Creates counterfactual candidates from an individual regarding a concept.
    Args: 
        concept: an OWLObject concept in ALCH
        data_file: link to an .owl ontology file
        individual: an individual of type OWLNamedIndividual in that ontology
        namespace: the namespace of that ontology
        goal_is_hold: set True if the goal is to make the concept hold, 
            False if goal is to make the concept not hold for the individual
        saving: set True to save the resulting changed KnowledgeBases
            containing the counterfactuals as .owl ontology files
        restrictions: features that must not be changed. Provide as list of
        OWLClasses and OWLObjectProperties
    
    
    __slots__ = '_concept', '_data_file', '_individual', '_namespace',\
        '_saving', '_goal_is_hold', 'restrictions', '_placeholder_count', \
        '_concept_TLDNF', '_concept_TLCNF', '_concept_as_list'\
        'candidate_dict', 'kb_dict', '_change_count', '_manager,\
        '_base_onto', '_base_reasoner', '_reasoner'
    
    restrictions: list
    '''
    
    def __init__(self, concept, data_file, individual,
                 namespace: str, goal_is_hold: bool = True, 
                 saving: bool = True, restrictions: list = None):

        self._concept = NNF().get_class_nnf(concept)
        self._data_file = data_file
        self._individual = individual
        self._namespace = namespace
        self._saving = saving
        self._placeholder_count = 0
        self._goal_is_hold = goal_is_hold
        self.restrictions = restrictions
        self._concept_TLDNF = None
        self._concept_TLCNF = None
        self._concept_as_list = None
        self.candidate_dict = None
        self.kb_dict = None
        self._change_count = None
        self.onto = KnowledgeBase(path=self._data_file).ontology()
        #self._manager = self.onto.get_owl_ontology_manager()
        
    def __repr__(self):
        return (f"CounterfactualCandidateGenerator('{self.concept}', "
                + f"{self._data_file}, {self._individual}, "
                + f"{self._namespace}, {self._saving})")
        
    def _create_list(self):
        '''
        - Brings concept to TLDNF/TLCNF
        - Creates list of lists of clauses of the concept to work with
        '''
        
        if self._goal_is_hold:       
            # Bring to top-level disjunctive normal form
            self._concept_TLDNF = TopLevelDNF().get_top_level_dnf(self._concept)
            disj_of_conj_list = [] 
            if type(self._concept_TLDNF) == OWLObjectUnionOf:
                for united in self._concept_TLDNF.operands():
                    if type(united) == OWLObjectIntersectionOf:
                        current_union = []
                        for intersected in united.operands():
                            current_union.append(intersected)
                        disj_of_conj_list.append(current_union)
                    else:
                        disj_of_conj_list.append(united)
            elif type(self._concept_TLDNF) == OWLObjectIntersectionOf:
                    current_union = []
                    for intersected in self._concept_TLDNF.operands():
                        current_union.append(intersected)
                    disj_of_conj_list.append(current_union)
            else:
                disj_of_conj_list.append(self._concept_TLDNF)
            return disj_of_conj_list

        else:  
            # This is the same as above, only the lists are in TLCNF not TLDNF
            self._concept_TLCNF = TopLevelCNF().get_top_level_cnf(self._concept)
            conj_of_disj_list = [] 
            if type(self._concept_TLCNF) == OWLObjectIntersectionOf:
                for intersected in self._concept_TLCNF.operands():
                    if type(intersected) == OWLObjectUnionOf:
                        current_intersection = []
                        for united in intersected.operands():
                            current_intersection.append(united)
                        conj_of_disj_list.append(current_intersection)
                    else:
                        conj_of_disj_list.append(intersected)
            elif type(self._concept_TLCNF) == OWLObjectUnionOf:
                    current_intersection = []
                    for united in self._concept_TLCNF.operands():
                        current_intersection.append(united)
                    conj_of_disj_list.append(current_intersection)
            else:
                conj_of_disj_list.append(self._concept_TLCNF)
            return conj_of_disj_list
    
    '''    
    # add c(x')        
    def _add_class(self, kb, class_concept, individual, reasoner, reasoner_sub):
        # Nothing
        if class_concept.is_owl_nothing():
            print("Individual that is 'Nothing' can not exist.")
            self._change_count = float('inf')
        # Add
        self._manager_editing.add_axiom(
            kb.ontology(),
            OWLClassAssertionAxiom(individual, 
                                   class_concept))
        # count
        if individual == self._individual:
            classes_list = list(reasoner.sub_classes(
                                            class_concept))
            classes_list.append(class_concept)
            new_classes = []
            for a_class in classes_list:
                if a_class not in list(reasoner.types(
                                individual, direct=False)):
                    new_classes.append(a_class)
            self._change_count = self._change_count + len(new_classes)
            
        # Subclasses of added classes are counted
    
    '''

    def _remove_class(self, kb, concept, individual):

            self._manager_editing.remove_axiom(
                kb.ontology(),
                OWLClassAssertionAxiom(individual, 
                                       concept))
        
        # Subclasses of removed classes are not counted
        
    def _make_hold(self, data_file, concept, individual):
        
        # Load reasoner    
        reasoner = OWLReasoner_Owlready2_ComplexCEInstances(
            KnowledgeBase(path=data_file).ontology(), 
            infer_property_values = False, 
            isolate = False)
        
        # Apply rewriting
        
        # Bring to tldnf
        
        #For clause in CC do
        for sub_list in self._concept_as_list: # "for clause in CC do"
                     
            kb = KnowledgeBase(path=data_file) # "K' ← copy(K)"
            self._manager = kb.ontology().get_owl_ontology_manager()
            
            if type(sub_list) != list:
                sub_list = [sub_list]
                
            for concept_part in sub_list: # "for C in clause do"
                
                if individual in reasoner.instances(concept, direct=False):
                    self.positive(kb, concept, individual)
                    
            reasoner_result = OWLReasoner_Owlready2_ComplexCEInstances(kb.ontology(), infer_property_values = True, isolate = False)
            if self._individual in reasoner_result.instances(self._concept):
                self.kb_dict[str(sub_list)] = kb

            # Save ontology file
                if self._saving:
                    if (os.path.exists(
                            f"/{os.getcwd()}/Candidate{kb_count}.owl"
                            )):
                        os.remove(
                            f"/{os.getcwd()}/Candidate{kb_count}.owl")
                    self._manager_editing.save_ontology(
                        kb.ontology(),
                        IRI.create(f'file:/Candidate{kb_count}.owl'))
    
                print(f"Candidate {kb_count} was created with "
                      + f"{self._change_count} axiom changes.\n"
                       f"The concept part was {str(sub_list)}.")
                self.candidate_dict[f'Candidate{kb_count}'] = {
                    "concept_part": str(sub_list),
                    "change_count": f'{self._change_count}'}
                kb_count = kb_count+1

    def _negative(kb, concept, individual):
      
        # handle restrictions if they exist - "c ∈ R"
        if self.restrictions != None:
            if isinstance(concept_part, OWLObjectComplementOf):
                check_if_restricted = concept_part.get_operand()
            else:
                check_if_restricted = concept_part
            if isinstance(check_if_restricted, OWLClass):
                if check_if_restricted in self.restrictions:
                    print("Restricted feature must not be changed.")
                    self._change_count = float('inf')            
                    continue
            elif isinstance(check_if_restricted, 
                          OWLObjectSomeValuesFrom)\
            or isinstance(check_if_restricted, 
                          OWLObjectAllValuesFrom):
                if check_if_restricted.get_property()\
                in self.restrictions:
                    self._change_count = float('inf')            
                    continue
            else:
                pass    
            
        # handle top concept
        elif class_concept.is_owl_thing():
            print("Individual that is not 'Thing' can not exist.")
            self._change_count = float('inf')
            
        # Complement of Class
        elif isinstance(concept, OWLObjectComplementOf):
            to_positive = concept.get_operand()
            self._positive(kb, to_positive, individual)
            
        else:
            # Class
            if isinstance(concept, OWLClass):
                self._remove_class(kb, concept, individual)
            
                # Existential restriction
                # remove all r(x, yi) with K |= D(yi )
            if isinstance(concept, OWLObjectSomeValuesFrom):
                
                role_name = concept.get_property().get_iri()._remainder
                role = concept.get_property()
                role_object_list = [] # list of other individuals y with r(x,y)
                for a_prop in props_list_names:
                    for y in list(reasoner.object_property_values(
                                    individual,
                                    role)):
                        role_object_list.append(y)
                role_object_list = list(OrderedDict.fromkeys(role_object_list))

                # Filler is Top concept (remove all r(x,y))
                if concept.get_filler().is_owl_thing():
                    for any_object in role_object_list:
                        property_remove = OWLObjectPropertyAssertionAxiom( 
                                        individual,                  
                                        OWLObjectProperty(                 
                                            IRI(self._namespace,
                                                f'{a_prop}')), 
                                        an_object)                                 
                        self._manager_editing.remove_axiom(onto, 
                                                            property_remove)

                # Filler is any other Concept D (remove only r(x,y) with D(y))
                else:
                    role_objects_in_restriction_concept = [] # y with D(y)
                    for an_object in role_object_list:
                        if an_object in list(reasoner_sub.instances(
                                        concept.get_filler())):
                            role_objects_in_restriction_concept.append(an_object)
                    # Removing
                    for relevant_object in role_objects_in_restriction_concept:
                        property_remove = OWLObjectPropertyAssertionAxiom(
                                            individual,
                                            role,
                                            relevant_object)
                        self._manager_editing.remove_axiom(onto,
                                                            property_remove)
            
                
            if universal:
                # add y, add r(x',y), hold(K, y, ¬D)
                if isinstance(concept, OWLObjectAllValuesFrom):
                
                    a_prop = concept._property
                    a_filler = concept._filler
                    placeholder_individual = OWLNamedIndividual(IRI(self._namespace, 
                        f'PH{self._placeholder_count}'))
                    property_add = OWLObjectPropertyAssertionAxiom(individual, 
                        a_prop, placeholder_individual)
                    self._manager_editing.add_axiom(onto, property_add) # Ontolearn creates the individual y automatically
                    self._placeholder_count = self._placeholder_count+1
                    
                    # the changed KB has to be saved and read again
                    # because of an unfixed issue in owlapy
                    if (os.path.exists('file:/temporary_kb_storage.owl')):
                        os.remove('file:/temporary_kb_storage.owl')
                    self._manager_editing.save_ontology(
                        onto, IRI.create('file:/temporary_kb_storage.owl'))
                    data_file_new = os.path.join(os.getcwd(), 'temporary_kb_storage.owl')
                    
                    self._make_hold(data_file_new, a_filler, placeholder_individual)       
        
        
        
        
'''       
        
        
        
        
        
        
        
        
        
        
        onto = kb.ontology()
        

        
        # Class
        # add c(x') 
        if isinstance(concept, OWLClass):
            self._add_class(kb, concept, individual, reasoner, reasoner_sub)
            
        # Existential restriction
        # add a, add r(x',a),positive A(a)
        elif isinstance(concept, OWLObjectSomeValuesFrom):
            a_prop = concept._property
            a_filler = concept._filler
            placeholder_individual = OWLNamedIndividual(IRI(self._namespace, 
                f'PH{self._placeholder_count}'))
            property_add = OWLObjectPropertyAssertionAxiom(individual, 
                a_prop, placeholder_individual)
            self._manager_editing.add_axiom(onto, property_add)
            self._placeholder_count = self._placeholder_count+1    
            
            # the changed KB has to be saved and read again
            # because of an unfixed issue in owlapy
            if (os.path.exists('file:/temporary_kb_storage.owl')):
                os.remove('file:/temporary_kb_storage.owl')
            self._manager_editing.save_ontology(
                onto, IRI.create('file:/temporary_kb_storage.owl'))
            data_file_new = os.path.join(os.getcwd(), 'temporary_kb_storage.owl')
            
            # create new reasoners for the changed KB
            manager_reasoning_new = OWLOntologyManager_Owlready2()            
            base_onto_new = manager_reasoning_new.load_ontology(
                                IRI.create(data_file_new))
            base_reasoner_new = OWLReasoner_Owlready2(base_onto_new)
            reasoner_new = OWLReasoner_FastInstanceChecker(
                                base_onto_new,
                                base_reasoner_new,
                                negation_default=True,
                                sub_properties=False)
            reasoner_sub_new = OWLReasoner_FastInstanceChecker(
                                    base_onto_new,
                                    base_reasoner_new,
                                    negation_default=True,
                                    sub_properties=True)
            
            self._make_hold(kb, a_filler, placeholder_individual, reasoner_new, reasoner_sub_new)
            # Counting
            if individual == self._individual:
                self._change_count = self._change_count+1
            
        # Universal Restriction
        # remove all statements r'(x',a) with r⊑r'and \|= A(a)
        if isinstance(concept, OWLObjectAllValuesFrom):
            role_name = concept.get_property().get_iri()._remainder
            role = OWLObjectProperty(IRI(self._namespace, f'{role_name}'))

            props_list = list(reasoner.sub_object_properties(role))
            props_list.append(role)
            props_list_names = []

            for g in props_list:
                props_list_names.append(g.get_iri()._remainder)
            role_object_list = []
            for a_prop in props_list_names:
                for y in list(reasoner.object_property_values(
                                individual,
                                OWLObjectProperty(
                                    IRI(self._namespace, f'{a_prop}')))):
                    role_object_list.append(y)
            role_object_list = list(OrderedDict.fromkeys(role_object_list))

            # If object is Thing:
                # This is fine: the code below will just remove ALL the
                # relevant object properties, since T holds for every object

            role_objects_in_restriction_concept = []
            for an_object in role_object_list:
                if an_object in list(reasoner_sub.instances(
                                OWLObjectComplementOf(concept.get_filler()))):
                    role_objects_in_restriction_concept.append(an_object)
            
            for a_prop in props_list_names:
                for relevant_object in role_objects_in_restriction_concept:
                    if relevant_object in list(reasoner.object_property_values(
                                    individual,
                                    OWLObjectProperty(
                                        IRI(self._namespace, f'{a_prop}')))):
                        # Counting
                        if individual == self._individual:
                            self._change_count = self._change_count+1
                        # Removing
                        property_remove = OWLObjectPropertyAssertionAxiom(
                                            individual,
                                            OWLObjectProperty(
                                                IRI(self._namespace, f'{a_prop}')),
                                            relevant_object)
                        self._manager_editing.remove_axiom(onto,
                                                            property_remove)

    def _make_not_hold(self, kb, concept, individual, reasoner, reasoner_sub):

        onto = kb.ontology()
        
        # Complement of Class
        if isinstance(concept, OWLObjectComplementOf):
            to_add = concept.get_operand()
            self._add_class(kb, to_add, individual, reasoner, reasoner_sub)


        
        # Universal Restriction
        
            
           
   
'''            
            
    def generate_candidates(self):

        kb_count = 0
        self._concept_as_list = self._create_list()
        self.candidate_dict = {}
        self.kb_dict = {}
        
        if self._goal_is_hold:            
            self._make_hold(self._data_file, self._concept_as_list, self._individual, self.kb_dict, self.restrictions)
        

        

        