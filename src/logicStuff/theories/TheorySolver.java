/*
 * Copyright (c) 2015 Ondrej Kuzelka
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

package logicStuff.theories;

import ida.ilp.logic.*;
import ida.ilp.logic.subsumption.Matching;
import ida.ilp.logic.subsumption.SpecialBinaryPredicates;
import ida.ilp.logic.subsumption.SpecialVarargPredicates;
import ida.utils.IntegerFunction;
import ida.utils.Sugar;
import ida.utils.tuples.Pair;
import ida.utils.tuples.Triple;

import java.util.*;

/**
 * Created by kuzelkao_cardiff on 06/02/15.
 */
public class TheorySolver {

    public static boolean DEBUG = false;

    private int subsumptionMode = Matching.THETA_SUBSUMPTION;

    private Set<Literal> deterministicLiterals;

    private Set<Pair<String, Integer>> deterministicPredicates = new HashSet<Pair<String, Integer>>();

    private SpecialBinaryPredicates specialBinaryPredicates = new SpecialBinaryPredicates();

    public final static int CUTTING_PLANES = 1, GROUND_ALL = 2;

    private int mode = CUTTING_PLANES;

    private int activeRuleSubsample = Integer.MAX_VALUE;

    private int activeRuleSubsamplingLevelStep = 1;

    private IntegerFunction restartSequence = new IntegerFunction.ConstantFunction(Integer.MAX_VALUE);

    private SatSolver satSolver = new SatSolver() {

        @Override
        public Set<Literal> solve(Collection<Clause> satProblem) {
            return new GroundTheorySolver(Sugar.setFromCollections(satProblem)).solve();
        }

        @Override
        public List<Set<Literal>> solveAll(Collection<Clause> satProblem, int maxCount) {
            return new GroundTheorySolver(Sugar.setFromCollections(satProblem)).solveAll(maxCount);
        }

        @Override
        public List<Set<Literal>> solveAll(Collection<Clause> satProblem, Set<Literal> groundAtoms, int maxCount) {
            return new GroundTheorySolver(Sugar.setFromCollections(satProblem), groundAtoms).solveAll(maxCount);
        }
    };

    public Set<Literal> solve(Collection<Clause> rules) {
        return this.solve(rules, Sugar.<Literal>set());
    }

    public Set<Literal> solve(Collection<Clause> rules, Set<Literal> evidence) {
        return this.solve(rules, evidence, Sugar.<Literal>set());
    }

    public Set<Literal> solve(Collection<Clause> rules, final Set<Literal> evidence, final Set<Literal> deterministic) {
        for (Literal d : deterministic) {
            this.deterministicPredicates.add(new Pair<String, Integer>(d.predicate(), d.arity()));
        }
        this.deterministicLiterals = deterministic;

        Set<Literal> state = new HashSet<Literal>();
        Set<Clause> initRules = new HashSet<Clause>();
        Pair<String, Integer> p = new Pair<String, Integer>();
        for (Literal e : evidence) {
            p.set(e.predicate(), e.arity());
            if (deterministicPredicates.contains(p)) {
                if ((e.isNegated() && deterministic.contains(e.negation())) || (!e.isNegated() && !deterministic.contains(e))) {
                    return null;
                }
            } else {
                if (!e.isNegated()) {
                    state.add(e);
                }
                initRules.add(new Clause(Sugar.list(e)));
            }
        }
        state.addAll(deterministic);
        Set<Clause> groundRules = new HashSet<Clause>();
        for (Clause rule : rules) {
            if (LogicUtils.isGround(rule)) {
                groundRules.add(rule);
            }
        }



        rules = Sugar.collectionDifference(rules, groundRules);


        initRules.addAll(groundRules);
        if (this.mode == GROUND_ALL) {
            initRules.addAll(groundAll(rules, state, Sugar.<Literal>set()));
        }
        initRules = Sugar.<Clause, Clause>funcallAndRemoveNulls(initRules, new Sugar.Fun<Clause, Clause>() {
            @Override
            public Clause apply(Clause clause) {
                if (isGroundClauseVacuouslyTrue(clause, deterministic)) {
                    return null;
                } else {
                    return removeSpecialAndDeterministicPredicates(clause);
                }
            }
        });

        Set<Clause> activeRules = new HashSet<Clause>(initRules);

        int iteration = 1;
        int restart = 0;
        while (true) {
            if (DEBUG) {
                System.out.println("Active rules: " + activeRules.size() + ", iteration: " + iteration);
            }
            //System.out.println(activeRules);
            if ((state = satSolver.solve(activeRules)) == null) {
                return null;
            }
            state.addAll(deterministic);

            Set<Clause> violatedRules = Sugar.setFromCollections(findViolatedRules(Sugar.union(rules, initRules), state));

            violatedRules = Sugar.<Clause, Clause>funcallAndRemoveNulls(violatedRules, new Sugar.Fun<Clause, Clause>() {
                @Override
                public Clause apply(Clause clause) {
                    if (isGroundClauseVacuouslyTrue(clause, deterministic)) {
                        System.out.println("weird: " + clause + ", ~~~" + LogicUtils.flipSigns(clause));
                        return null;
                    } else {
                        return removeSpecialAndDeterministicPredicates(clause);
                    }
                }
            });

            activeRules.addAll(violatedRules);

            iteration++;
            if (violatedRules.isEmpty()) {
                //sanity checkq
                if (this.activeRuleSubsample != Integer.MAX_VALUE) {
                    this.activeRuleSubsample = Integer.MAX_VALUE;
                    if (!findViolatedRules(rules, state).isEmpty()) {
                        throw new IllegalStateException();
                    }
                }
                break;
            }
            if (iteration >= this.restartSequence.f(restart)){
                Set<Clause> oldActiveRules = activeRules;
                activeRules = new HashSet<Clause>(initRules);//Sugar.union(violatedRules, initRules);
//                for (Clause c : oldActiveRules){
//                    if (Math.random() < 0.1){
//                        activeRules.add(c);
//                    }
//                }
                iteration = 0;
                restart++;
            }
        }
        return state;
    }

    public List<Set<Literal>> solveAll(Collection<Clause> rules, final Set<Literal> evidence, final Set<Literal> deterministic, int maxCount) {
        return solveAll(rules, evidence, deterministic, null, maxCount);
    }

    public List<Set<Literal>> solveAll(Collection<Clause> rules, final Set<Literal> evidence, final Set<Literal> deterministic, Set<Literal> groundAtoms, int maxCount){
        return solveAll(rules, evidence, deterministic, groundAtoms, maxCount, maxCount);
    }

    public List<Set<Literal>> solveAll(Collection<Clause> rules, final Set<Literal> evidence, final Set<Literal> deterministic, int maxReturnedCount, int maxTriedCount){
        return solveAll(rules, evidence, deterministic, null, maxReturnedCount, maxTriedCount);
    }

    public List<Set<Literal>> solveAll(Collection<Clause> rules, final Set<Literal> evidence, final Set<Literal> deterministic, Set<Literal> groundAtoms, int maxReturnedCount, int maxTriedCount) {
        for (Literal d : deterministic) {
            this.deterministicPredicates.add(new Pair<String, Integer>(d.predicate(), d.arity()));
        }
        this.deterministicLiterals = deterministic;

        Set<Literal> fixedState = new HashSet<Literal>();

        Set<Clause> initRules = new HashSet<Clause>();
        Pair<String, Integer> p = new Pair<String, Integer>();
        for (Literal e : evidence) {
            p.set(e.predicate(), e.arity());
            if (deterministicPredicates.contains(p)) {
                if ((e.isNegated() && deterministic.contains(e.negation())) || (!e.isNegated() && !deterministic.contains(e))) {
                    return new ArrayList<Set<Literal>>();
                }
            } else {
                if (!e.isNegated()) {
                    fixedState.add(e);
                }
                initRules.add(new Clause(Sugar.list(e)));
            }
        }
        fixedState.addAll(deterministic);
        Set<Clause> groundRules = new HashSet<Clause>();
        for (Clause rule : rules) {
            if (LogicUtils.isGround(rule)) {
                groundRules.add(rule);
            }
            if (rule.literals().isEmpty()){
                return new ArrayList<Set<Literal>>();
            }
        }
        rules = Sugar.collectionDifference(rules, groundRules);
        initRules.addAll(groundRules);
        initRules = Sugar.<Clause, Clause>funcallAndRemoveNulls(initRules, new Sugar.Fun<Clause, Clause>() {
            @Override
            public Clause apply(Clause clause) {
                if (isGroundClauseVacuouslyTrue(clause, deterministic)) {
                    return null;
                } else {
                    return removeSpecialAndDeterministicPredicates(clause);
                }
            }
        });

        Set<Clause> activeRules = new HashSet<Clause>();
        activeRules.addAll(initRules);

        if (this.mode == GROUND_ALL) {
            activeRules.addAll(groundAll(rules, evidence, groundAtoms));
            activeRules = Sugar.<Clause, Clause>funcallAndRemoveNulls(activeRules, new Sugar.Fun<Clause, Clause>() {
                @Override
                public Clause apply(Clause clause) {
                    if (isGroundClauseVacuouslyTrue(clause, deterministic)) {
                        return null;
                    } else {
                        return removeSpecialAndDeterministicPredicates(clause);
                    }
                }
            });
            return satSolver.solveAll(activeRules, groundAtoms, maxReturnedCount);
        } else {
            int mc = 1;
            Set<Set<Literal>> retVal = new HashSet<Set<Literal>>();
            do {
                int iteration = 1;
                mc = Math.min(2 * mc, maxTriedCount);
                while (true) {
                    System.out.println("Active rules: " + activeRules.size() + ", iteration: " + iteration);
                    List<Set<Literal>> candidateSolutions = satSolver.solveAll(activeRules, groundAtoms, mc);
                    if (candidateSolutions.isEmpty()) {
                        return candidateSolutions;
                    }
                    int numViolatedRules = 0;
                    for (Set<Literal> solution : candidateSolutions) {
                        Set<Clause> violatedRules = Sugar.setFromCollections(findViolatedRules(Sugar.union(rules, initRules), Sugar.union(solution, deterministic)));
                        violatedRules = Sugar.<Clause, Clause>funcallAndRemoveNulls(violatedRules, new Sugar.Fun<Clause, Clause>() {
                            @Override
                            public Clause apply(Clause clause) {
                                if (isGroundClauseVacuouslyTrue(clause, deterministic)) {
                                    System.out.println("weird: " + clause + ", ~~~" + LogicUtils.flipSigns(clause));
                                    return null;
                                } else {
                                    return removeSpecialAndDeterministicPredicates(clause);
                                }
                            }
                        });
                        if (violatedRules.isEmpty()) {
                            retVal.add(solution);
                        } else {
                            numViolatedRules += violatedRules.size();
                            activeRules.addAll(violatedRules);
                        }
                    }
                    iteration++;
                    if (numViolatedRules == 0 || retVal.size() >= maxReturnedCount) {
                        //sanity check
                        for (Set<Literal> solution : retVal) {
                            //System.out.println(solution);
                            if (this.activeRuleSubsample != Integer.MAX_VALUE) {
                                this.activeRuleSubsample = Integer.MAX_VALUE;
                                if (!findViolatedRules(rules, solution).isEmpty()) {
                                    throw new IllegalStateException();
                                }
                            }
                        }
                        break;
                    }
                }
            } while (mc < maxReturnedCount && retVal.size() >= mc);
            return Sugar.listFromCollections(retVal);
        }
    }

    public List<Clause> findViolatedRules(Collection<Clause> rules, Set<Literal> currentState){
        List<Clause> violated = new ArrayList<Clause>();
        Set<Constant> constants = LogicUtils.constants(rules);
        for (Literal l : currentState){
            for (int i = 0; i < l.arity(); i++){
                if (constants.contains(l.get(i))){
                    constants.remove(l.get(i));
                }
            }
        }

        Literal constantIntroductionLiteral = new Literal("", true, constants.size());

        int constantIndex = 0;
        for (Constant c : constants){
            constantIntroductionLiteral.set(c, constantIndex++);
        }

        Matching matching = newM(new Clause(Sugar.union(currentState, constantIntroductionLiteral)));
        for (Clause rule : rules){
            if (this.activeRuleSubsample == Integer.MAX_VALUE) {
                Pair<Term[], List<Term[]>> substitutions = matching.allSubstitutions(LogicUtils.flipSigns(rule), 0, Integer.MAX_VALUE);
                for (Term[] subs : substitutions.s) {
                    violated.add(LogicUtils.substitute(rule, substitutions.r, subs));
                }
            } else {
                Pair<Term[], List<Term[]>> substitutions0 = matching.allSubstitutions(LogicUtils.flipSigns(rule), 0, this.activeRuleSubsample);
                if (substitutions0.s.size() < this.activeRuleSubsample){
                    for (Term[] subs : substitutions0.s) {
                        violated.add(LogicUtils.substitute(rule, substitutions0.r, subs));
                    }
                } else {
                    Triple<Term[], List<Term[]>, Double> substitutions = matching.searchTreeSampler(LogicUtils.flipSigns(rule), 0, this.activeRuleSubsample, this.activeRuleSubsamplingLevelStep);
                    for (Term[] subs : substitutions.s) {
                        violated.add(LogicUtils.substitute(rule, substitutions.r, subs));
                    }
                }
            }
        }
        return violated;
    }

    public List<Clause> groundAll(Collection<Clause> rules, Set<Literal> evidence, Set<Literal> groundAtoms){
        List<Clause> groundRules = new ArrayList<Clause>();
        Matching matching;
        Set<Constant> constantsInGroundAtoms = LogicUtils.constants(new Clause(groundAtoms));
        Literal constantIntroduction = new Literal("", Sugar.listFromCollections(constantsInGroundAtoms));
        if (this.deterministicLiterals != null) {
            matching = newM(new Clause(Sugar.union(this.deterministicLiterals, evidence, Sugar.list(constantIntroduction))));
        } else {
            matching = newM(new Clause(Sugar.union(evidence, groundAtoms)));
        }
        matching.setSubsumptionMode(this.subsumptionMode);
        for (Clause rule : rules){
            Clause stub = ruleStub(rule);
            Pair<Term[], List<Term[]>> substitutions = matching.allSubstitutions(LogicUtils.flipSigns(stub), 0, Integer.MAX_VALUE);
            for (Term[] subs : substitutions.s) {
                groundRules.add(LogicUtils.substitute(rule, substitutions.r, subs));
                //System.out.println(rule+" --> "+LogicUtils.substitute(rule, substitutions.r, subs));
            }
        }

        return groundRules;
    }

    private Clause ruleStub(Clause rule){
        Set<String> specialPredicates = Sugar.setFromCollections(SpecialBinaryPredicates.SPECIAL_PREDICATES, SpecialVarargPredicates.SPECIAL_PREDICATES);
        Set<Literal> newLiterals = new HashSet<Literal>();
        Pair<String,Integer> pair = new Pair<String,Integer>();
        for (Literal l : rule.literals()){
            pair.set(l.predicate(),l.arity());
            if (specialPredicates.contains(l.predicate()) || deterministicPredicates.contains(pair)){
                newLiterals.add(l);
            }
        }
        Set<Variable> variables = rule.variables();
        Literal variablesIntroduction = new Literal(SpecialVarargPredicates.TRUE, true, variables.size());
        int i = 0;
        for (Variable var : variables){
            variablesIntroduction.set(var, i++);
        }
        newLiterals.add(variablesIntroduction);
        return new Clause(newLiterals);
    }

    private boolean isGroundClauseVacuouslyTrue(Clause c, Set<Literal> deterministic){
        for (Literal l : c.literals()){
            if (SpecialVarargPredicates.SPECIAL_PREDICATES.contains(l.predicate()) || SpecialBinaryPredicates.SPECIAL_PREDICATES.contains(l.predicate())){
                Boolean b = isSpecialGroundTrue(l);
                return b != null && b.booleanValue();
            } else if (this.deterministicPredicates.contains(new Pair<String,Integer>(l.predicate(), l.arity()))){
                if ((!l.isNegated() && deterministic.contains(l)) || (l.isNegated() && !deterministic.contains(l.negation()))){
                    return true;
                }
            }
        }
        return false;
    }

    private Clause removeSpecialAndDeterministicPredicates(Clause clause){
        List<Literal> filtered = new ArrayList<Literal>();
        Set<String> specialPredicates = Sugar.setFromCollections(SpecialBinaryPredicates.SPECIAL_PREDICATES, SpecialVarargPredicates.SPECIAL_PREDICATES);
        for (Literal literal : clause.literals()){
            if (!specialPredicates.contains(literal.predicate()) &&
                    !deterministicPredicates.contains(new Pair<String,Integer>(literal.predicate(), literal.arity()))){
                filtered.add(literal);
            }
        }
        return new Clause(filtered);
    }

    private boolean isSpecialGroundTrue(Literal l){
        if (SpecialBinaryPredicates.SPECIAL_PREDICATES.contains(l.predicate())){
            return specialBinaryPredicates.isTrueGround(l);
        } else if (SpecialVarargPredicates.SPECIAL_PREDICATES.contains(l.predicate())){
            return SpecialVarargPredicates.isTrueGround(l);
        }
        return false;
    }

    private Matching newM(){
        Matching m = new Matching();
        m.setSubsumptionMode(this.subsumptionMode);
        return m;
    }

    private Matching newM(Clause clause){
        Matching m = new Matching(Sugar.<Clause>list(clause));
        m.setSubsumptionMode(this.subsumptionMode);
        return m;
    }

    public void setActiveRuleSubsampling(int numSamples){
        this.activeRuleSubsample = numSamples;
    }

    public void setActiveRuleSubsamplingLevelStep(int levelStep){
        this.activeRuleSubsamplingLevelStep = levelStep;
    }

    public void setMode(int mode){
        this.mode = mode;
    }

    public void setSatSolver(SatSolver solver){
        this.satSolver = solver;
    }

    public void setSubsumptionMode(int subsumptionMode){
        this.subsumptionMode = subsumptionMode;
    }


    public static void main(String[] args){
        Clause a = Clause.parse("bond(id1,id2)");
        Clause c = Clause.parse("e(id1,id2)");
        Clause b = Clause.parse("!bond(X,Y),bond(Y,X)");

        List<Clause> theory = Sugar.list(a, b,c);
        Set<Literal> set = new TheorySolver().solve(theory);
        for (Literal literal : set) {
            boolean implied = TheorySimplifier.isGroundLiteralImplied(literal, theory);
            if (implied){
                System.out.println("is in\t"+literal);
            }
        }
        System.out.println(set);
    }


}
