/*
 * Copyright (c) 2015 Ondrej Kuzelka
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

package logicStuff.learning;

import ida.ilp.logic.*;
import ida.ilp.logic.special.IsoClauseWrapper;
import ida.utils.Sugar;
import ida.utils.tuples.Pair;
import logicStuff.theories.TheorySimplifier;

import java.util.*;

/**
 * Created by ondrejkuzelka on 01/02/17.
 */
public class ShortConstraintLearner {

    private int maxVariables = 3;

    private int maxLength = 2;

    private Dataset dataset;

    private Set<Pair<String,Integer>> allPredicates;

    public ShortConstraintLearner(Dataset dataset){
        this.dataset = dataset;
        this.allPredicates = this.dataset.allPredicates();
    }

    public ShortConstraintLearner(Dataset dataset, int maxLength, int maxVariables){
        this(dataset);
        this.maxLength = maxLength;
        this.maxVariables = maxVariables;
    }

    /**
     * The learned constraints are assumed to have an implicit alldiff on all variables but this alldiff is not added
     * explicitly! To correctly use this type of rules with the TheorySolver, use theorySolver.setSubsumptionMode(Matching.OI_SUBSUMPTION).
     * @return
     */
    public List<Clause> learnConstraints(){
        Set<IsoClauseWrapper> constraints = new HashSet<IsoClauseWrapper>();
        Set<IsoClauseWrapper> beam = new HashSet<IsoClauseWrapper>();
        beam.add(new IsoClauseWrapper(new Clause()));
        for (int i = 0; i < maxLength; i++){
            Set<IsoClauseWrapper> newBeam = new HashSet<IsoClauseWrapper>();
            for (IsoClauseWrapper c : beam){
                for (Clause cand : refinements(c.getOriginalClause())) {
                    if (!dataset.matches(cand)) {
                        if (minimal(cand, dataset)) {
                            constraints.add(new IsoClauseWrapper(LogicUtils.flipSigns(cand)));
                        }
                    } else if (cand.countLiterals() < maxLength) {
                        newBeam.add(new IsoClauseWrapper(cand));
                    }
                }
            }
            beam = newBeam;
        }
        int numVars = 0;
        Set<Clause> retVal = new HashSet<Clause>();
        for (IsoClauseWrapper icw : constraints){
            retVal.add(icw.getOriginalClause());
            numVars = Math.max(numVars, icw.getOriginalClause().variables().size());
        }
        return TheorySimplifier.simplify(retVal, numVars + 1);
//        return Sugar.listFromCollections(retVal);
    }

    //quick naive hack
    private boolean minimal(Clause cand, Dataset dataset){
        for (Literal l : cand.literals()){
            if (!dataset.matches(new Clause(Sugar.collectionDifference(cand.literals(), l)))){
                return false;
            }
        }
        return true;
    }

    private List<Clause> refinements(Clause clause){
        Set<IsoClauseWrapper> set = new HashSet<IsoClauseWrapper>();
        for (Pair<String,Integer> predicate : allPredicates){
            for (Clause newClause : Sugar.union(refinements(clause, predicate, true), refinements(clause, predicate, false))) {
                set.add(new IsoClauseWrapper(newClause));
            }
        }
        List<Clause> retVal = new ArrayList<Clause>();
        for (IsoClauseWrapper icw : set){
            retVal.add(icw.getOriginalClause());
        }
        return retVal;
    }

    private List<Clause> refinements(Clause clause, Pair<String,Integer> predicate, boolean negated){
        Map<IsoClauseWrapper,Literal> refinements = new HashMap<IsoClauseWrapper,Literal>();
        Set<Variable> variables = clause.variables();
        Set<Variable> freshVariables = LogicUtils.freshVariables(variables, predicate.s);
        Literal freshLiteral = LogicUtils.newLiteral(predicate.r, predicate.s, freshVariables);
        if (negated){
            freshLiteral = freshLiteral.negation();
        }

        Clause init = new Clause(Sugar.union(clause.literals(), freshLiteral));
        refinements.put(new IsoClauseWrapper(init), freshLiteral);

        for (int i = 0; i < predicate.s; i++){
            Map<IsoClauseWrapper,Literal> newRefinements = new HashMap<IsoClauseWrapper, Literal>();
            for (Map.Entry<IsoClauseWrapper,Literal> entry : refinements.entrySet()){
                Variable x = (Variable)entry.getValue().get(i);
                for (Variable v : entry.getKey().getOriginalClause().variables()){
                    if (v != x){
                        Clause substituted = LogicUtils.substitute(entry.getKey().getOriginalClause(), x, v);
                        Literal newLiteral = LogicUtils.substitute(entry.getValue(), x, v);
                        if (substituted.countLiterals() > clause.countLiterals() && !substituted.containsLiteral(newLiteral.negation())) {
                            HornClause candidate = new HornClause(substituted);
                            Clause candClause = candidate.toClause();
                            newRefinements.put(new IsoClauseWrapper(candClause), newLiteral);
                        }
                    }
                }
            }
            refinements.putAll(newRefinements);
        }
        Set<IsoClauseWrapper> refinementSet = refinements.keySet();
        List<Clause> retVal = new ArrayList<Clause>();
        for (IsoClauseWrapper icw : refinementSet){
            if (icw.getOriginalClause().variables().size() <= this.maxVariables) {
                retVal.add(icw.getOriginalClause());
            }
        }
        return retVal;
    }

    public static void main(String[] args) throws Exception {
        Clause db = Clause.parse("a(x1),a(x2),b(x3),b(x4),e(x1,x2),e(x2,x1)");
        ShortConstraintLearner url = new ShortConstraintLearner(new Dataset(db));

        List<Clause> rules = url.learnConstraints();
        for (Clause c : rules){
            System.out.println(c);
        }

    }

}
