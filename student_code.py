import read, copy
from util import *
from logical_classes import *

verbose = 0

class KnowledgeBase(object):
    def __init__(self, facts=[], rules=[]):
        self.facts = facts
        self.rules = rules
        self.ie = InferenceEngine()

    def __repr__(self):
        return 'KnowledgeBase({!r}, {!r})'.format(self.facts, self.rules)

    def __str__(self):
        string = "Knowledge Base: \n"
        string += "\n".join((str(fact) for fact in self.facts)) + "\n"
        string += "\n".join((str(rule) for rule in self.rules))
        return string

    def _get_fact(self, fact):
        """INTERNAL USE ONLY
        Get the fact in the KB that is the same as the fact argument

        Args:
            fact (Fact): Fact we're searching for

        Returns:
            Fact: matching fact
        """
        for kbfact in self.facts:
            if fact == kbfact:
                return kbfact

    def _get_rule(self, rule):
        """INTERNAL USE ONLY
        Get the rule in the KB that is the same as the rule argument

        Args:
            rule (Rule): Rule we're searching for

        Returns:
            Rule: matching rule
        """
        for kbrule in self.rules:
            if rule == kbrule:
                return kbrule

    def kb_add(self, fact_rule):
        """Add a fact or rule to the KB
        Args:
            fact_rule (Fact|Rule) - the fact or rule to be added
        Returns:
            None
        """
        printv("Adding {!r}", 1, verbose, [fact_rule])
        if isinstance(fact_rule, Fact):
            if fact_rule not in self.facts:
                self.facts.append(fact_rule)
                for rule in self.rules:
                    self.ie.fc_infer(fact_rule, rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.facts.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.facts[ind].supported_by.append(f)
                else:
                    ind = self.facts.index(fact_rule)
                    self.facts[ind].asserted = True
        elif isinstance(fact_rule, Rule):
            if fact_rule not in self.rules:
                self.rules.append(fact_rule)
                for fact in self.facts:
                    self.ie.fc_infer(fact, fact_rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.rules.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.rules[ind].supported_by.append(f)
                else:
                    ind = self.rules.index(fact_rule)
                    self.rules[ind].asserted = True

    def kb_assert(self, fact_rule):
        """Assert a fact or rule into the KB

        Args:
            fact_rule (Fact or Rule): Fact or Rule we're asserting
        """
        printv("Asserting {!r}", 0, verbose, [fact_rule])
        self.kb_add(fact_rule)

    def kb_ask(self, fact):
        """Ask if a fact is in the KB

        Args:
            fact (Fact) - Statement to be asked (will be converted into a Fact)

        Returns:
            listof Bindings|False - list of Bindings if result found, False otherwise
        """
        print("Asking {!r}".format(fact))
        if factq(fact):
            f = Fact(fact.statement)
            bindings_lst = ListOfBindings()
            # ask matched facts
            for fact in self.facts:
                binding = match(f.statement, fact.statement)
                if binding:
                    bindings_lst.add_bindings(binding, [fact])

            return bindings_lst if bindings_lst.list_of_bindings else []

        else:
            print("Invalid ask:", fact.statement)
            return []

    def kb_retract(self, fact_or_rule):
        """Retract a fact from the KB

        Args:
            fact (Fact) - Fact to be retracted

        Returns:
            None
        """
        printv("Retracting {!r}", 0, verbose, [fact_or_rule])
        ####################################################
        # Student code goes here

        # if input fact_or_rule(fr) neither Fact nor Rule, ignore it
        if not isinstance(fact_or_rule,Fact) or not isinstance(fact_or_rule, Rule):
            return

        # o.w check if it is Fact or Rule, start from Fact...
        else:
            # if input fr is Fact
            if instance(fact_or_rule,Fact):
                # retrieve fr from KB: rules[]
                fact = self._get_fact(fact_or_rule)

                # if retracting fr is Fact Asserted and Supported, keep it
                if fact.asserted and fact.supported_by:
                    print("fact is Asserted and Supported, keep it")
                    return

                # if retracting fr not supported, start to remove it...
                if not fact.supported_by:
                    print("fact is not supported, start to remove it from kb...")

                    # verify if any support_fact supported by retracting fr
                    # # 找到全部要删的fact所支持的fact：support_fact
                    for support_fact in fact.supports_facts:
                        # f_r below is [fact, rule] belongs to support_fact, which is supported by retracting fr
                        for f_r in support_fact.supported_by:
                            # for all retracting fr in support_fact:
                            # if retracing fr in child's parents, remove child from all kb
                            if fact in f_r:
                                kb_rule = self._get_rule(f_r[1])
                                kb_rule.supports_facts.remove(support_fact)

                                kb_support_fact = self._get_fact(support_fact)
                                kb_support_fact.supported_by.remove(f_r)

                        #if kb_support_fact.supported_by == []:
                        if not kb_support_fact.supported_by:
                            self.kb_retract(kb_support_fact)

                    # 找到全部要删的fact所支持的rule：support_rule
                    for support_rule in fact.supports_rules:
                        # 在所有support_rule集合中，找到它包含的支持的子fact和rule里：f_r

                        for f_r in support_rule.supported_by:
                                # 若发现需要被删的fact也存在于这些子fact和rule里，
                                # 则把含有需要删除的fact的rule:f_r中的rule挑出来，删除

                            if fact in f_r:
                                kb_rule = self._get_rule(f_r[1])
                                kb_rule.supported_by.remove(support_rule)
                                # 同时 把子集合support_rule里的rule找到
                                # 然后，把支持的support_rule里rule的rule和fact: f_r也删除
                                kb_support_rule = self._get_rule(support_rule)
                                kb_support_rule.supported_by.remove(f_r)

                        #if kb_support_rule ==[]:
                        if not kb_support_rule.asserted:
                            self.kb_retract(kb_support_rule)

                    # so far all facts retracted, remove them from knowledge base
                    self.facts.remove(fact)

            elif isinstance(fact_or_rule,Rule):
                # if rule has been asserted, cannot retracted
                if rule.asserted:
                    print("asserted rule cannot be removed")
                    return

                # if rule not asserted, proceed to retract
                else:
                    # retrieve fr from KB: rules[]
                    rule = self._get_rule(fact_or_rule)

                    if not rule.supported_by:
                        print("rule not asserted, start to remove it from kb...")

                        # 对于rule所派生出的fact：
                        for support_fact in rule.supports_facts:
                            # 对于派生出上述fact的fact和rule：
                            for f_r in support_fact.supported_by:
                                # 若 要删的rule在上述派生出的rule里：
                                if rule in f_r:
                                #【先】 remove 从rule里派生出的fact：support_fact
                                    # 在KB里找到派生出support_fact的fact
                                    kb_fact = self._get_fact(f_r[0])
                                    # 把rule派生出的fact:support_fact 从KB里删除
                                    kb_fact.supports_facts.remove(support_fact)

                                #【再】 remove support_fact 被支持的rule:
                                    # 在KB里找到support_fact派生出的fact
                                    kb_support_fact = self._get_fact(support_fact)
                                    kb_support_fact.supported_by.remove(f_r)

                            #if kb_support_fact == []:
                            if not kb_support_fact.supported_by:
                                self.kb_retract(kb_support_fact)

                        # 对于rule所派生出的rule:
                        for support_rule in rule.supports_rules:
                            for f_r in support_rule.supported_by:
                                if rule in f_r:
                                #【先】 remove 从rule里派生出的fact：support_fact
                                    # 在KB里找到派生出support_fact的fact
                                    kb_fact = self._get_fact(f_r[0])
                                    # 把rule派生出的fact:support_fact 从KB里删除
                                    kb_fact.supports_facts.remove(support_fact)
                                #【再】 remove support_rule 被支持的rule:
                                    # 在KB里找到support_rule派生出的rule
                                    kb_support_rule = self._get_rule(support_rule)
                                    kb_support_rule.supported_by.remove(f_r)

                        if not kb_support_rule.asserted:
                                    self.kb_retract(kb_support_rule)

                    self.rules.remove(rule)

            else:
                print("fact either suportted or removed")

        return

class InferenceEngine(object):
    def fc_infer(self, fact, rule, kb):
        """Forward-chaining to infer new facts and rules

        Args:
            fact (Fact) - A fact from the KnowledgeBase
            rule (Rule) - A rule from the KnowledgeBase
            kb (KnowledgeBase) - A KnowledgeBase

        Returns:
            Nothing            
        """
        printv('Attempting to infer from {!r} and {!r} => {!r}', 1, verbose,
            [fact.statement, rule.lhs, rule.rhs])
        ####################################################
        # Student code goes here

        # Step 1:     match if input fact's statement binding with exiting rule's most left fact's statement
        # Step 2:     use function instantiate() to pass binding constants across rule: both lhs & rhs
        # Step 3:     if above binding is true,
        #             then: check if existing rule most left contains more than 1 fact:

        # Step 3.1:   yes -> let remaining part of (lhs facts => rhs fact) to be a NEW_RULE,
        #                    using function Rule() to assign new_rule supported by input fact and rule
        # Step 3.1.1: add new_rule to kb() using function kb_add()
        # Step 3.1.2: add new_rule into the list of supports_rules that current input fact supports
        # Step 3.1.3: add new_rule into the list of supports_rules that current input rule supports
        bindings = match(fact.statement,rule.lhs[0])
        if bindings:
            if len(rule.lhs)>1:
                new_rule_lhs = [instantiate(remaining_facts,bindings) for remaining_facts in rule.lhs[1:]]
                new_rule_rhs = instantiate(rule.rhs,bindings)
                new_rule = Rule([new_rule_lhs,new_rule_rhs],supported_by=[fact,rule])
                kb.kb_add(new_rule)
                fact.supports_rules.append(new_rule)
                rule.supports_rules.append(new_rule)

        # Step 3.2:   no  -> draw conclusion from rule_rhs,
        #                    using function instantiate() to pass binding constants replacing rule.rhs, which is a fact
        #                    using function Fact() to assign new_fact supported by input fact and rule
        # Step 3.2.1: add new_fact to kb() using function kb_add()
        # Step 3.2.2: add new_fact into the list of supports_rules that current input fact supports
        # Step 3.2.3: add new_fact into the list of supports_rules that current input rule supports
            else:
                new_rule_rhs = instantiate(rule.rhs, bindings)
                new_fact = Fact(new_rule_rhs,supported_by= [fact,rule])
                kb.kb_add(new_fact)
                fact.supports_facts.append(new_fact)
                rule.supports_facts.append(new_fact)
        else:
            pass

        # Conslusion: now having new rule or new fact supported by input fact and rule


















