package logicStuff.learning;/*
 * Copyright (c) 2015 Ondrej Kuzelka
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */


import ida.ilp.logic.*;
import ida.ilp.logic.subsumption.ApproximateSubsetCounter;
import ida.ilp.logic.subsumption.Matching;
import ida.ilp.logic.subsumption.SpecialVarargPredicates;
import ida.utils.Cache;
import ida.utils.Combinatorics;
import ida.utils.MutableDouble;
import ida.utils.Sugar;
import ida.utils.collections.MultiList;
import ida.utils.collections.MultiMap;
import ida.utils.tuples.Pair;
import logicStuff.Globals;
import logicStuff.theories.TheorySolver;

import java.util.*;

/**
 * Created by kuzelkao_cardiff on 25/01/17.
 */
public class Dataset {

    private static final int PLAIN_MODE = 1;

    public final static int SUBSAMPLING_MODE = 2;

    private int mode = SUBSAMPLING_MODE;

    private static double[] defaultSubsamples = {/*0.33,0.66,*/1};

    private Dataset[] subsamples;

    private ArrayList<Literal> queries;

    private ArrayList<Boolean> targets;

    private double positiveWeight = 0.5, negativeWeight = 0.5;

    private double numPositive, numNegative;

    private Clause example;

    private Set<Constant> allConstants;

    private Set<Pair<String,Integer>> allPredicates;

    private Set<Pair<String,Integer>> queryPredicates = new HashSet<Pair<String, Integer>>();

    private Matching matching;

    private ApproximateSubsetCounter subsetCounter;

    private Cache<Clause,Boolean> matchingCache = new Cache<Clause, Boolean>();

    public Dataset(Clause example){
        set(example, null, null, SUBSAMPLING_MODE);
    }

    public Dataset(Clause example, int mode){
        set(example, null, null, mode);
    }

    //targets: true if query should be implied, false otherwise (i.e. either if !query should be implied
    //or if neither query nor !query should be implied)
    public Dataset(Clause example, List<Literal> queries, List<Boolean> targets, int mode){
        set(example, queries, targets, mode);
    }

    public Dataset(Clause example, Collection<Literal> positiveExamples, Collection<Literal> negativeExamples, int mode){
        List<Literal> queries = new ArrayList<Literal>();
        queries.addAll(positiveExamples);
        queries.addAll(negativeExamples);
        List<Boolean> targets = new ArrayList<Boolean>();
        for (int i = 0; i < positiveExamples.size(); i++){
            targets.add(Boolean.TRUE);
        }
        for (int i = 0; i < negativeExamples.size(); i++){
            targets.add(Boolean.FALSE);
        }
        set(example, queries, targets, mode);
    }

    private void set(Clause example, List<Literal> queries, List<Boolean> targets, int mode){
        this.example = example;
        this.mode = mode;
        this.allConstants = LogicUtils.constants(example);
        this.matching = new Matching(Sugar.<Clause>list(example));
        //we assume alldiff(...) constraints over all variables in rules
        this.matching.setSubsumptionMode(Matching.OI_SUBSUMPTION);
        this.subsetCounter = new ApproximateSubsetCounter(example, 0.5, 1);
        this.subsetCounter.setSubsumptionMode(Matching.OI_SUBSUMPTION);
        this.allPredicates = LogicUtils.predicates(this.example);
        if (queries != null) {
            this.queries = new ArrayList<Literal>(queries);
            for (Literal l : queries) {
                this.queryPredicates.add(new Pair<String, Integer>(l.predicate(), l.arity()));
            }
        }
        if (targets != null) {
            this.targets = new ArrayList<Boolean>(targets);
            for (Boolean target : targets) {
                if (target) {
                    this.numPositive++;
                } else {
                    this.numNegative++;
                }
            }
        }
        if (mode == SUBSAMPLING_MODE){
            this.subsamples = new Dataset[defaultSubsamples.length];
//            for (int i = 0; i < defaultSubsamples.length; i++){
//                int num = (int)(this.example.countLiterals()*defaultSubsamples[i]);
//                this.subsamples[i] = new Dataset(new Clause(Combinatorics.randomCombination(Sugar.listFromCollections(example.literals()), num).toList()), queries, targets, SUBSET_MODE);
//            }
            Clause previous = this.example;
            for (int i = defaultSubsamples.length-1; i >= 0; i--){
                int num = (int)(this.example.countLiterals()*defaultSubsamples[i]);
                Clause next = new Clause(Combinatorics.randomCombination(Sugar.listFromCollections(previous.literals()), num).toList());
                this.subsamples[i] = new Dataset(next, queries, targets, PLAIN_MODE);
                previous = next;
            }
        }
    }

    public double accuracy(List<HornClause> rules, int k){
        /*if (this.mode == SUBSET_MODE){
            double avgPosCovered = 0;
            double avgNegCovered = 0;
            for (int i = 0; i < queries.size(); i++){
                Literal query = queries.get(i);
                Boolean target = targets.get(i);
                List<Clause> unifiedClauses = new ArrayList<Clause>();
                for (HornClause rule : rules) {
                    rule = addAlldiffConstraint(rule, Math.min(k, rule.variables().size()));
                    Clause c = rule.unify(query);
                    if (c != null){
                        unifiedClauses.add(LogicUtils.flipSigns(c));
                    }
                }
                double logNumCoveringSets = subsetCounter.logApproxCount(unifiedClauses, k);
                double logBinom = Combinatorics.logBinomial(allConstants.size(), k)/Math.log(2);
                if (target){
                    avgPosCovered += Math.pow(2.0, logNumCoveringSets-logBinom);
                } else {
                    avgNegCovered += Math.pow(2.0, logNumCoveringSets-logBinom);
                }
            }
            return (positiveWeight*avgPosCovered+negativeWeight*(numNegative-avgNegCovered))/(positiveWeight*numPositive+negativeWeight*numNegative);
        } else*/ if (mode == SUBSAMPLING_MODE){
            double avgPosCovered = 0;
            double avgNegCovered = 0;
            for (Dataset subsample : subsamples) {
                for (int i = 0; i < queries.size(); i++) {
                    Literal query = queries.get(i);
                    Boolean target = targets.get(i);
                    List<Clause> unifiedClauses = new ArrayList<Clause>();
                    for (HornClause rule : rules) {
                        rule = addAlldiffConstraint(rule, k);
                        Clause c = rule.unify(query);
                        //System.out.println("unified: "+c);
                        if (c != null) {
                            unifiedClauses.add(LogicUtils.flipSigns(c));
                        }
                    }
                    boolean covers = false;
                    for (Clause unified : unifiedClauses){
//                        if (subsample.matching.subsumption(unified, 0)){
//                            covers = true;
//                            break;
//                        }
                        if (subsample.subsumption(unified)){
                            covers = true;
                            break;
                        }
                    }
                    if (covers) {
                        if (target) {
                            avgPosCovered += 1.0/subsamples.length;
                        } else {
                            avgNegCovered += 1.0/subsamples.length;
                        }
                    }
                }
            }
            double retVal = (positiveWeight*avgPosCovered+negativeWeight*(numNegative-avgNegCovered))/(positiveWeight*numPositive+negativeWeight*numNegative);
            //System.out.println(rules+", pos: "+avgPosCovered+", neg: "+avgNegCovered+", acc: "+retVal+", pos weight: "+positiveWeight+", neg weight: "+negativeWeight);
            return retVal;
        } else {
            throw new IllegalArgumentException();
        }
    }

    private boolean subsumption(Clause unified){
        if (unified == null) {
            return false;
        }
//        Boolean quickCheck;
//        if ((quickCheck = this.matchingCache.get(unified)) !=  null){
//            return quickCheck;
//        }
//        Set<IsoClauseWrapper> subclauses = new HashSet<IsoClauseWrapper>();
//        for (Literal l : unified.literals()){
//            subclauses.add(new IsoClauseWrapper(new Clause(Sugar.collectionDifference(unified.literals(), l))));
//        }
//        for (IsoClauseWrapper icw : subclauses){
//            Boolean covered = this.matchingCache.get(unified);
//            if (covered != null){
//                if (!covered.booleanValue()){
//                    this.matchingCache.put(unified, Boolean.FALSE);
//                    System.out.println("Saved subsumption");
//                    return false;
//                }
//            }
//        }
//        boolean result = this.matching.subsumption(unified, 0);
//        this.matchingCache.put(unified, result);
//        return result;
        return this.matching.subsumption(unified, 0);
    }

    private HornClause addAlldiffConstraint(HornClause hc, int k){
        Clause c = hc.toClause();
        int numTerms = c.terms().size();
        Literal alldiffConstraint = new Literal(SpecialVarargPredicates.ALLDIFF, true, numTerms);
        int i = 0;
        for (Term t : c.terms()){
            alldiffConstraint.set(t,i);
            i++;
        }
        return new HornClause(new Clause(Sugar.union(c.literals(), alldiffConstraint)));
//        Clause c = hc.toClause();
//        int numTerms = c.terms().size();
//        Literal maxCardConstraint = new Literal(SpecialVarargPredicates.MAX_CARD, true, Math.max(numTerms,k)+1);
//        Literal alldiffConstraint = new Literal(SpecialVarargPredicates.ALLDIFF, true, Math.max(numTerms,k));
//        int i = 0;
//        maxCardConstraint.set(Constant.construct(String.valueOf(k)), i++);
//        for (Term t : c.terms()){
//            maxCardConstraint.set(t, i);
//            alldiffConstraint.set(t,i-1);
//            i++;
//        }
//        if (numTerms < k) {
//            for (Variable v : LogicUtils.freshVariables(Sugar.setFromCollections(c.variables()), k-numTerms)) {
//                maxCardConstraint.set(v,i);
//                i++;
//            }
//        }
//        return new HornClause(new Clause(Sugar.union(c.literals(), Sugar.list(maxCardConstraint, alldiffConstraint))));
    }

    public int numPositiveMatchedExistentially(HornClause rule, int k, int maxNum) {
        int retVal = 0;
        rule = addAlldiffConstraint(rule, k);
        for (int i = 0; i < queries.size(); i++){
            if (targets.get(i)) {
                Literal query = queries.get(i);
                Clause c = rule.unify(query);
                if (c != null) {
                    if (this.subsumption(LogicUtils.flipSigns(c))/*matching.subsumption(LogicUtils.flipSigns(c), 0)*/) {
                        retVal++;
                    }
                }
                if (retVal >= maxNum) {
                    return retVal;
                }
            }
        }
        return retVal;
    }

    public boolean matches(Clause clause) {
        return this.matching.subsumption(clause, 0);
    }

    public void addQueryPredicate(String predicateName, int arity){
        this.queryPredicates.add(new Pair<String, Integer>(predicateName, arity));
    }

    public Set<Pair<String, Integer>> queryPredicates() {
        return this.queryPredicates;
    }

    public Set<Pair<String, Integer>> allPredicates() {
        return this.allPredicates;
    }

    public List<Literal> queries(){
        return this.queries;
    }

    public List<Boolean> targets(){
        return this.targets;
    }

    public Collection<Literal> literals(){
        return this.example.literals();
    }

    public void setWeights(double positiveWeight, double negativeWeight){
        this.positiveWeight = positiveWeight;
        this.negativeWeight = negativeWeight;
    }

    public static List<Literal> possibleExamples(Clause db, String predicateName, int arity, List<Clause> hardRules){
        return possibleExamples(db, predicateName, arity, hardRules, Integer.MAX_VALUE, null);
    }

    public static List<Literal> possibleExamples(Clause db, String predicateName, int arity, List<Clause> hardRules, int desiredNum, Random random){
        return possibleExamples(db, predicateName, arity, hardRules, desiredNum, random, new MutableDouble(0));
    }

    public static List<Literal> possibleExamples(Clause db, String predicateName, int arity, List<Clause> hardRules, int desiredNum, Random random, MutableDouble estimatedCount){

        List<Clause> theory = new ArrayList<Clause>();
        theory.addAll(hardRules);

        TheorySolver ts = new TheorySolver();
        ts.setSubsumptionMode(Matching.OI_SUBSUMPTION);

        List<Clause> theoryAndEvidence = new ArrayList<Clause>();
        theoryAndEvidence.addAll(theory);
        for (Literal l : db.literals()){
            theoryAndEvidence.add(new Clause(l));
        }

        Clause fastCheckDB = new Clause(ts.solve(theoryAndEvidence));

        MultiList<Pair<String,Integer>,Constant> typing = typing(db);
        int max = 1;
        for (int i = 0; i < arity; i++){
            max *= typing.get(new Pair<String,Integer>(predicateName,i)).size();
        }
        desiredNum = (int)(0.8*Math.min(max, desiredNum));

        List<Constant> candidateConstants = typing.get(new Pair<String,Integer>(predicateName,0));

        Set<Literal> retVal0 = new HashSet<Literal>();
        int maxTries = desiredNum*5;
        int ok = 0;
        int chunk = 100;
        int tries = 0;
        for (int i = 0; i < maxTries; i++){
            Set<Literal> newLs = new HashSet<Literal>();
            Set<Literal> additionalDBLits = new HashSet<Literal>();
            for (int j = 0; j < chunk; j++) {
                Literal newL = new Literal(predicateName, arity);
                for (int k = 0; k < arity; k++) {
                    List<Constant> t = typing.get(new Pair<String, Integer>(predicateName, k));
                    newL.set(t.get(random.nextInt(t.size())), k);
                }
                newLs.add(newL);
                Set<Literal> sol = ts.solve(theory, Sugar.set(newL));
                if (sol != null){
                    additionalDBLits.addAll(sol);
                }
            }

            if (ts.findViolatedRules(theory, Sugar.union(fastCheckDB.literals(), additionalDBLits, newLs)).isEmpty()){
                retVal0.addAll(newLs);
                ok += newLs.size();
                tries += chunk;
                //System.out.println("ok chunk");
            } else {
                for (Literal newL : newLs) {
                    List<Clause> testTheory = new ArrayList<Clause>();
                    testTheory.addAll(theory);
                    testTheory.add(new Clause(newL));
                    for (Literal dbLit : db.literals()) {
                        testTheory.add(new Clause(dbLit));
                    }
                    if (ts.solve(testTheory) != null) {
                        ok++;
                        retVal0.add(newL);
                    }
                    tries++;
                }
            }
            if (retVal0.size() >= desiredNum){
                double est = (double)ok/(double)tries;
                for (int j = 0; j < arity; j++) {
                    est *= typing.get(new Pair<String, Integer>(predicateName, j)).size();
                }
                estimatedCount.set(est);
                return Sugar.listFromCollections(retVal0);
            }
            if (tries > 30 && retVal0.size()/(double)tries < 0.2){
                break;
            }
        }

        List<Literal> current = new ArrayList<Literal>();
        current.add(LogicUtils.newLiteral(predicateName, arity));

        double mult = 1.0;
        for (int i = 0; i < arity; i++){
            List<Clause> slice = theorySlice(theory, predicateName, arity, 0, i+1);

            List<Clause> sliceTheory = new ArrayList<Clause>(slice);

            for (Literal l : db.literals()){
                slice.add(new Clause(l));
            }
            List<Literal> next = new ArrayList<Literal>();
            List<Pair<Literal,Constant>> candidates = new ArrayList<Pair<Literal, Constant>>();

            for (Constant c : i == 0 ? candidateConstants : typing.get(new Pair<String,Integer>(predicateName,i))/*possibleConstants(db, candidateConstants, theory, predicateName, arity, i)*/) {
                for (Literal l : current) {
                    candidates.add(new Pair<Literal, Constant>(l, c));
                }
            }
            if (Globals.verbose){
                System.out.println("Num candidate constant-literal pairs: "+candidates.size());
            }
            Collections.shuffle(candidates, random);
            int k = 0;
            for (Pair<Literal,Constant> pair : candidates){
                Literal newL = new Literal(predicateName, i+1);
                for (int j = 0; j < i; j++){
                    newL.set(pair.r.get(j), j);
                }
                newL.set(pair.s, i);


                if (ts.findViolatedRules(sliceTheory, Sugar.union(fastCheckDB.literals(), newL)).isEmpty()){
                    next.add(newL);
                    //System.out.println("pass: "+newL);
                } else if (ts.solve(Sugar.union(slice, new Clause(newL))) != null){
                    next.add(newL);
                }
                if (next.size() >= desiredNum){
                    mult *= (candidates.size()/(double)desiredNum);
                    break;
                }
                k++;
            }
            current = next;
        }
        estimatedCount.set(current.size()*mult);
        return current;
    }



    private static MultiList<Pair<String,Integer>,Constant> typing(Clause db){
        MultiMap<Pair<String,Integer>,Constant> mm = new MultiMap<Pair<String, Integer>, Constant>();
        for (Literal l : db.literals()){
            for (int i = 0; i < l.arity(); i++){
                mm.put(new Pair<String,Integer>(l.predicate(),i),(Constant)l.get(i));
            }
        }
        MultiMap<Pair<String,Integer>,Constant> retVal = new MultiMap<Pair<String, Integer>, Constant>();
        for (Map.Entry<Pair<String,Integer>,Set<Constant>> entry1 : mm.entrySet()){
            for (Map.Entry<Pair<String,Integer>,Set<Constant>> entry2 : mm.entrySet()){
                if (!Sugar.intersection(entry1.getValue(), entry2.getValue()).isEmpty()){
                    retVal.putAll(entry1.getKey(), entry1.getValue());
                    retVal.putAll(entry1.getKey(), entry2.getValue());
                    retVal.putAll(entry2.getKey(), entry1.getValue());
                    retVal.putAll(entry2.getKey(), entry2.getValue());
                }
            }
        }
        return retVal.toMultiList();
    }

    private static List<Constant> possibleConstants(Clause db, Collection<Constant> candidateConstants, List<Clause> theory, String predicateName, int arity, int index){
        List<Constant> retVal = new ArrayList<Constant>();
        List<Clause> slice = theorySlice(theory, predicateName, arity, index, index+1);
        List<Clause> sliceTheory = new ArrayList<Clause>(slice);

        TheorySolver ts = new TheorySolver();
        ts.setSubsumptionMode(Matching.OI_SUBSUMPTION);

        Clause fastCheckDB = new Clause(ts.solve(theory, db.literals()));

        for (Literal l : db.literals()) {
            slice.add(new Clause(l));
        }
        for (Constant c : candidateConstants) {
            Literal newL = new Literal(predicateName, 1);
            newL.set(c, 0);

            /*if (ts.findViolatedRules(sliceTheory, Sugar.union(fastCheckDB.literals(), newL)).isEmpty()){
                retVal.add(c);
                //System.out.println("pass(2): "+newL);
            } else*/ if (ts.solve(Sugar.union(slice, new Clause(newL))) != null){
                retVal.add(c);
            }
        }
        return retVal;
    }

    private static List<Clause> theorySlice(List<Clause> theory, String predicate, int arity, int start, int end){
        List<Clause> retVal = new ArrayList<Clause>();
        outerLoop: for (Clause c : theory){
            if (!c.predicates().contains(predicate)){
                retVal.add(c);
            } else {
                List<Literal> l1 = new ArrayList<Literal>();
                List<Literal> l2 = new ArrayList<Literal>();
                for (Literal l : c.literals()){
                    if (l.predicate().equals(predicate) && l.arity() == arity){
                        l1.add(l);
                    } else {
                        l2.add(l);
                    }
                }
                List<Literal> l3 = new ArrayList<Literal>();
                for (Literal l : l1){
                    for (int i : outerIntervals(start, end, arity)){
                        int count = 0;
                        for (Literal byTerm : c.getLiteralsByTerm(l.get(i))){
                            for (int j = 0; j < byTerm.arity(); j++){
                                if (byTerm.get(j).equals(l.get(i))){
                                    count++;
                                }
                            }
                            if (count > 1) {
                                continue outerLoop;
                            }
                        }
                    }
                    Literal shorter = new Literal(l.predicate(), l.isNegated(), end-start);
                    int j = 0;
                    for (int i = start; i < end; i++){
                        shorter.set(l.get(i), j++);
                    }
                    l3.add(shorter);
                }
                retVal.add(new Clause(Sugar.union(l2,l3)));
            }
        }
        return retVal;
    }

    private static int[] outerIntervals(int start, int end, int length){
        int[] retVal = new int[start+length-end];
        int j = 0;
        for (int i = 0; i < start; i++){
            retVal[j] = i;
            j++;
        }
        for (int i = end; i < length; i++){
            retVal[j] = i;
            j++;
        }
        return retVal;
    }

    public Dataset[] subsampledDatasets(){
        return this.subsamples;
    }

    public int datasetMode(){
        return this.mode;
    }

    public Set<Constant> constants(){
        return this.allConstants;
    }

    public double approxMatchingSubsets(Collection<Clause> rules, int k){
        rules = LogicUtils.standardizeApart(rules);
        if (LogicUtils.variables(rules).size() == 0){
            return Combinatorics.logBinomial(this.allConstants.size(), k)/Math.log(2);
        }
        List<Clause> queries = new ArrayList<Clause>();
        for (Clause c : rules){
            Set<Variable> vars = c.variables();
            if (vars.size() <= k) {
                Literal alldiff = new Literal(SpecialVarargPredicates.ALLDIFF, k);
                int j = 0;
                for (Variable v : c.variables()) {
                    alldiff.set(v, j++);
                }
                if (j < k){
                    for (Variable v : LogicUtils.freshVariables(vars, k-vars.size())){
                        alldiff.set(v, j++);
                    }
                }
                queries.add(new Clause(Sugar.union(LogicUtils.flipSigns(c.literals()), alldiff)));
            }
        }
        return Math.exp(Combinatorics.logBinomial(this.allConstants.size(), k))-Math.pow(2.0,subsetCounter.logApproxCount(queries, k));
    }

    protected Matching getMatchingObject(){
        return this.matching;
    }

}
