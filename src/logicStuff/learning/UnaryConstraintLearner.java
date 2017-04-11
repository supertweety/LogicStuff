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

import ida.ilp.logic.Clause;
import ida.ilp.logic.Literal;
import ida.ilp.logic.Term;
import ida.ilp.logic.Variable;
import ida.utils.Sugar;
import ida.utils.collections.MultiMap;
import ida.utils.collections.ValueToIndex;
import logicStuff.theories.GroundTheorySolver;

import java.util.*;

/**
 * Created by kuzelkao_cardiff on 01/02/17.
 */
public class UnaryConstraintLearner {

    private Clause dataset;

    private int maxLength = 5;

    public UnaryConstraintLearner(Clause dataset){
        this.dataset = dataset;
    }

    public UnaryConstraintLearner(Clause dataset, int maxLength){
        this(dataset);
        this.maxLength = maxLength;
    }

    public List<Clause> learnRules(){
        BinaryDataset binaryDataset = toPropositionalDataset();
        ConstraintLearner cl = new ConstraintLearner();
        Set<Clause> constraints = cl.learnConstraints(binaryDataset, this.maxLength);
        List<Clause> retVal = new ArrayList<Clause>();
        for (Clause c : constraints){
            retVal.add(c);
        }
        for (int i = 0; i < retVal.size(); i++){
            retVal.set(i, lift(retVal.get(i)));
        }
        return GroundTheorySolver.simplify(retVal);
        //return retVal;
    }

    private Clause lift(Clause c){
        List<Literal> literals = new ArrayList<Literal>();
        Variable x = Variable.construct("X");
        for (Literal l : c.literals()){
            literals.add(new Literal(l.predicate(), l.isNegated(), x));
        }
        return new Clause(literals);
    }

    private BinaryDataset toPropositionalDataset(){
        Set<String> attributeSet = new HashSet<String>();
        MultiMap<Term,Literal> examples = new MultiMap<Term, Literal>();
        for (Literal l : this.dataset.literals()){
            if (l.arity() == 1){
                examples.put(l.get(0), l);
                attributeSet.add(l.predicate());
            }
        }
        for (Term term : this.dataset.terms()){
            if (!examples.containsKey(term)){
                examples.set(term, Sugar.<Literal>set());
            }
        }
        String[] attributes = new String[attributeSet.size()];
        ValueToIndex<String> attributeToIndex = new ValueToIndex<String>();
        for (String predicate : attributeSet) {
            attributes[attributeToIndex.valueToIndex(predicate)] = predicate;
        }
        boolean[][] data = new boolean[examples.size()][attributes.length];
        int i = 0;
        for (Map.Entry<Term,Set<Literal>> entry : examples.entrySet()){
            for (Literal l : entry.getValue()){
                data[i][attributeToIndex.valueToIndex(l.predicate())] = true;
            }
            i++;
        }
        BinaryDataset retVal = new BinaryDataset(data, attributes);
        return retVal;
    }

    public void setMaxLength(int maxLength){
        this.maxLength = maxLength;
    }

    public static void main(String[] args) throws Exception {
        Clause db = Clause.parse("a(x),b(y)");
        UnaryConstraintLearner url = new UnaryConstraintLearner(db);
        url.setMaxLength(8);

        List<Clause> rules = url.learnRules();
        for (Clause c : rules){
            System.out.println(c);
        }

    }

}
