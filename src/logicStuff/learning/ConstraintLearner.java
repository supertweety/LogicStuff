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
import ida.ilp.logic.LogicUtils;
import ida.utils.Sugar;

import java.util.HashSet;
import java.util.Set;

/**
 * Created by kuzelkao_cardiff on 01/02/17.
 */
public class ConstraintLearner {

    public ConstraintLearner(){

    }

    public Set<Clause> learnConstraints(BinaryDataset dataset, int maxLength){
        Set<Clause> retVal = new HashSet<Clause>();
        Set<Clause> beam = new HashSet<Clause>();
        String[] attributes = dataset.attributes();
        beam.add(new Clause());
        for (int i = 0; i < attributes.length; i++){
            Set<Clause> newBeam = new HashSet<Clause>();
            for (Clause c : beam){
                Clause cand1 = new Clause(Sugar.union(c.literals(), new Literal(attributes[i])));
                if (dataset.count(cand1.literals()) == 0){
                    if (minimal(cand1, dataset)) {
                        retVal.add(LogicUtils.flipSigns(cand1));
                    }
                } else if (cand1.countLiterals() < maxLength){
                    newBeam.add(cand1);
                }
                Clause cand2 = new Clause(Sugar.union(c.literals(), new Literal(attributes[i], true)));
                if (dataset.count(cand2.literals()) == 0){
                    if (minimal(cand2, dataset)) {
                        retVal.add(LogicUtils.flipSigns(cand2));
                    }
                } else if (cand2.countLiterals() < maxLength){
                    newBeam.add(cand2);
                }
                newBeam.add(c);
            }
            beam = newBeam;
        }
        return retVal;
    }

    //quick naive hack
    private boolean minimal(Clause cand, BinaryDataset dataset){
        for (Literal l : cand.literals()){
            if (dataset.count(Sugar.collectionDifference(cand.literals(), l)) == 0){
                return false;
            }
        }
        return true;
    }

}
