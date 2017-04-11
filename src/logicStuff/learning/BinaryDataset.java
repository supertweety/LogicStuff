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
import ida.utils.Sugar;
import ida.utils.VectorUtils;
import ida.utils.collections.MultiMap;
import ida.utils.collections.ValueToIndex;
import ida.utils.tuples.Pair;

import java.io.IOException;
import java.io.PrintWriter;
import java.io.Reader;
import java.io.Writer;
import java.util.*;

/**
 * Created by kuzelkao_cardiff on 20/01/16.
 *
 *
 *
 */
public class BinaryDataset {

    public static enum FormulaType {
            CONJUNCTION, DISJUNCTION;
    };

    private String[] attributeNames;

    private HashMap<String,Integer> attributesToIndices = new HashMap<String,Integer>();

    private boolean[][] dataset;

    private double[] weights;

    public BinaryDataset(){}

    public BinaryDataset(boolean[][] dataset){
        this(dataset, null);
    }

    public BinaryDataset(boolean[][] dataset, String[] attributeNames){
        double[] w = new double[dataset.length];
        Arrays.fill(w, 1.0);
        this.set(dataset, attributeNames, w);
    }

    public BinaryDataset(boolean[][] dataset, String[] attributeNames, double[] weights) {
        this.set(dataset, attributeNames, weights);
    }

    public void set(boolean[][] dataset, String[] attributeNames, double[] weights) {
        this.dataset = dataset;
        this.weights = weights;
        this.attributeNames = attributeNames;
        if (this.attributeNames != null) {
            for (int i = 0; i < attributeNames.length; i++) {
                this.attributesToIndices.put(this.attributeNames[i], i);
            }
        }
        if (this.dataset.length > 0 && attributeNames == null) {
            this.attributeNames = new String[this.dataset[0].length];
            for (int i = 0; i < this.attributeNames.length; i++) {
                this.attributeNames[i] = String.valueOf(i);
                this.attributesToIndices.put(this.attributeNames[i], i);
            }
        }
    }

    public static BinaryDataset fromFeatures(MultiMap<String,String> features){
        ValueToIndex<String> vti = new ValueToIndex<String>(0);
        for (String feature : Sugar.flatten(features.values())){
            vti.valueToIndex(feature);
        }
        int numAttributes = vti.size();
        boolean[][] data = new boolean[features.keySet().size()][];
        int i = 0;
        for (Map.Entry<String,Set<String>> entry : features.entrySet()){
            boolean[] row = VectorUtils.falses(numAttributes);
            for (String feature : entry.getValue()){
                row[vti.valueToIndex(feature)] = true;
            }
            data[i] = row;
            i++;
        }
        String[] attributeNames = new String[numAttributes];
        for (String attributeName : vti.values()){
            attributeNames[vti.valueToIndex(attributeName)] = attributeName;
        }
        return new BinaryDataset(data, attributeNames);
    }

    public static BinaryDataset fromRows(Collection<boolean[]> rows, String[] attributeNames){
        boolean[][] data = new boolean[rows.size()][];
        int i = 0;
        for (boolean[] row : rows){
            data[i] = row;
            i++;
        }
        return new BinaryDataset(data, attributeNames);
    }

    public String[] attributes(){
        return this.attributeNames;
    }

    public int numExamples(){
        return this.dataset.length;
    }

    public double sumOfWeights(){
        return VectorUtils.sum(this.weights);
    }

    public void shuffle(Random random){
        VectorUtils.shuffle(this.dataset, random);
    }

    public BinaryDataset subDataset(int from, int to){
        boolean[][] d = new boolean[to-from][];
        double[] ws = new double[to-from];
        int j = 0;
        for (int i = from; i < to; i++){
            d[j] = this.dataset[i];
            ws[j] = this.weights[i];
            j++;
        }
        return new BinaryDataset(d, this.attributeNames, ws);
    }

    public BinaryDataset project(String[] attributes){
        return project(Sugar.set(attributes));
    }

    public BinaryDataset project(Set<String> attributes){
        int[] indices = new int[Sugar.intersection(Sugar.set(this.attributes()), attributes).size()];
        int index = 0;
        for (int j = 0; j < this.attributeNames.length; j++){
            if (attributes.contains(this.attributeNames[j])){
                indices[index] = j;
                index++;
            }
        }
        boolean[][] newData = new boolean[this.dataset.length][];
        for (int i = 0; i < newData.length; i++){
            boolean[] newRow = new boolean[indices.length];
            boolean[] oldRow = this.dataset[i];
            for (int j = 0; j < newRow.length; j++){
                newRow[j] = oldRow[indices[j]];
            }
            newData[i] = newRow;
        }
        String[] newAttributesNames = new String[indices.length];
        for (int i = 0; i < indices.length; i++){
            newAttributesNames[i] = this.attributeNames[indices[i]];
        }
        return new BinaryDataset(newData, newAttributesNames, this.weights);
    }

    public double enclosingHyperCubeVolume(){
        if (this.dataset.length == 0){
            return 0;
        }
        double volume = 1;
        int[] min = new int[this.attributeNames.length];
        Arrays.fill(min, 1);
        int[] max = new int[this.attributeNames.length];
        Arrays.fill(max, 0);
        for (boolean[] row : this.dataset){
            for (int i = 0; i < row.length; i++){
                if (row[i]){
                    max[i] = 1;
                } else {
                    min[i] = 0;
                }
            }
        }
        for (int i = 0; i < min.length; i++){
            volume *= (1+max[i]-min[i]);
        }
        return volume;
    }

    //[yes,no]
    public Pair<BinaryDataset,BinaryDataset> splitOnAttribute(String attribute){
        int attributeIndex = this.attributesToIndices.get(attribute);
        int yesCount = 0;
        for (boolean[] row : this.dataset){
            if (row[attributeIndex]){
                yesCount++;
            }
        }
        double[] yesWeights = new double[yesCount];
        double[] noWeights = new double[dataset.length-yesCount];
        boolean[][] yesData = new boolean[yesCount][];
        boolean[][] noData =  new boolean[dataset.length-yesCount][];
        int yesIndex = 0, noIndex = 0, index = 0;
        for (boolean[] row : this.dataset){
            if (row[attributeIndex]){
                yesData[yesIndex] = row;
                yesWeights[yesIndex] = this.weights[index];
                yesIndex++;
            } else {
                noData[noIndex] = row;
                noWeights[noIndex] = this.weights[index];
                noIndex++;
            }
            index++;
        }
        return new Pair<BinaryDataset,BinaryDataset>(new BinaryDataset(yesData, this.attributeNames, yesWeights), new BinaryDataset(noData, this.attributeNames, noWeights));
    }

    private boolean check(boolean[] row, String[] attributes, boolean[] positive, FormulaType formulaType){
        if (formulaType == FormulaType.CONJUNCTION) {
            for (int i = 0; i < attributes.length; i++) {
                if (row[this.attributesToIndices.get(attributes[i])] != positive[i]) {
                    return false;
                }
            }
            return true;
        } else if (formulaType == FormulaType.DISJUNCTION){
            for (int i = 0; i < attributes.length; i++) {
                if (row[this.attributesToIndices.get(attributes[i])] == positive[i]) {
                    return true;
                }
            }
            return false;
        }
        throw new UnsupportedOperationException("");
    }

    public double count(Clause clause){
        String[] attributes = new String[clause.countLiterals()];
        boolean[] positive = new boolean[attributes.length];
        int i = 0;
        for (Literal l : clause.literals()){
            attributes[i] = l.predicate();
            positive[i] = l.isNegated();
            i++;
        }
        return numExamples()-count(attributes, positive);
    }


    public BinaryDataset select(Clause clause){
        List<boolean[]> selectedRows = new ArrayList<boolean[]>();
        String[] attributes = new String[clause.countLiterals()];
        boolean[] positive = new boolean[attributes.length];
        int i = 0;
        for (Literal l : clause.literals()){
            attributes[i] = l.predicate();
            positive[i] = !l.isNegated();
            i++;
        }
        return select(attributes, positive, FormulaType.DISJUNCTION);
    }

    public BinaryDataset select(String[] attributes, boolean[] positive, FormulaType formulaType){
        List<boolean[]> rows = new ArrayList<boolean[]>();
        for (boolean[] row : this.dataset){
            if (check(row, attributes, positive, formulaType)){
                rows.add(row);
            }
        }
        boolean[][] newData = new boolean[rows.size()][];
        int i = 0;
        for (boolean[] row : rows){
            newData[i++] = row;
        }
        return new BinaryDataset(newData, this.attributeNames);
    }

    public double sum(Clause clause){
        String[] attributes = new String[clause.countLiterals()];
        boolean[] positive = new boolean[attributes.length];
        int i = 0;
        for (Literal l : clause.literals()){
            attributes[i] = l.predicate();
            positive[i] = l.isNegated();
            i++;
        }
        return sumOfWeights()-sum(attributes, positive);
    }

    public double approximateSum(Clause clause, int numSamples, Random random){
        String[] attributes = new String[clause.countLiterals()];
        boolean[] positive = new boolean[attributes.length];
        int i = 0;
        for (Literal l : clause.literals()){
            attributes[i] = l.predicate();
            positive[i] = l.isNegated();
            i++;
        }
        return sumOfWeights()*((double)numSamples/numExamples())-approximateSum(attributes, positive, numSamples, random);
    }

    public double count(Set<Literal> conjunction){
        String[] attributes = new String[conjunction.size()];
        boolean[] positive = new boolean[attributes.length];
        int i = 0;
        for (Literal l : conjunction){
            attributes[i] = l.predicate();
            positive[i] = !l.isNegated();
            i++;
        }
        return count(attributes, positive);
    }

    public double sum(Set<Literal> conjunction){
        String[] attributes = new String[conjunction.size()];
        boolean[] positive = new boolean[attributes.length];
        int i = 0;
        for (Literal l : conjunction){
            attributes[i] = l.predicate();
            positive[i] = !l.isNegated();
            i++;
        }
        return sum(attributes, positive);
    }

    public double count(String[] attributes, boolean[] positive){
        double retVal = 0;
        for (boolean[] row : this.dataset){
            if (check(row, attributes, positive, FormulaType.CONJUNCTION)){
                retVal++;
            }
        }
        return retVal;
    }

    public double sum(String[] attributes, boolean[] positive){
        double retVal = 0;
        int i = 0;
        for (boolean[] row : this.dataset){
            if (check(row, attributes, positive, FormulaType.CONJUNCTION)){
                retVal += this.weight(i);
            }
            i++;
        }
        return retVal;
    }

    public double approximateSum(String[] attributes, boolean[] positive, int numSamples, Random random){
        double retVal = 0;
        if (this.dataset.length == 0){
            return 0;
        }
        for (int i = 0; i < numSamples; i++){
            int index = random.nextInt(this.dataset.length);
            boolean[] row = this.dataset[index];
            if (check(row, attributes, positive, FormulaType.CONJUNCTION)){
                retVal += this.weight(index);
            }
            i++;
        }
        return retVal;
    }

    private boolean[][] rowsToMatrix(List<boolean[]> list){
        boolean[][] retVal = new boolean[list.size()][];
        for (int i = 0; i < list.size(); i++){
            retVal[i] = list.get(i);
        }
        return retVal;
    }

    public void writeCSV(Writer writer) throws IOException {
        PrintWriter pw = new PrintWriter(writer);
        pw.println(header());
        for (boolean[] row : this.examples()){
            pw.println(rowToString(row));
        }
        pw.flush();
    }

    private String header(){
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < this.attributeNames.length; i++){
            sb.append(attributeNames[i]);
            if (i < this.attributeNames.length-1){
                sb.append(",");
            }
        }
        return sb.toString();
    }

    private static String rowToString(boolean[] row){
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < row.length; i++){
            sb.append(row[i] ? "1" : "0");
            if (i < row.length-1){
                sb.append(",");
            }
        }
        return sb.toString();
    }

    public static BinaryDataset readCSV(Reader reader) throws IOException {
        int lineCounter = 0;
        List<boolean[]> parsedLines = new ArrayList<boolean[]>();
        String[] header = null;
        for (String line : Sugar.readLines(reader)){
            line = line.trim();
            if (line.length() > 0){
                if (lineCounter == 0 && isHeaderLine(line)){
                    header = parseHeaderRow(line);
                } else {
                    parsedLines.add(parseBooleanRow(line));
                }
                lineCounter++;
            }
        }
        boolean[][] data = new boolean[parsedLines.size()][];
        for (int i = 0; i < parsedLines.size(); i++){
            data[i] = parsedLines.get(i);
        }
        return new BinaryDataset(data, header);
    }

    private static String[] parseHeaderRow(String line){
        line = line.trim();
        if (line.charAt(line.length()-1) == ','){
            line = line.substring(0, line.length()-1);
        }
        String[] split = line.split(",");
        for (int i = 0; i < split.length; i++){
            split[i] = split[i].trim();
        }
        return split;
    }

    private static boolean[] parseBooleanRow(String line){
        line = line.trim();
        if (line.charAt(line.length()-1) == ','){
            line = line.substring(0, line.length()-1);
        }
        String[] split = line.split(",");
        for (int i = 0; i < split.length; i++){
            split[i] = split[i].trim();
        }
        boolean[] row = new boolean[split.length];
        for (int i = 0; i < split.length; i++){
            if (split[i].equalsIgnoreCase("t") || split[i].equalsIgnoreCase("1") || split[i].equalsIgnoreCase("true")){
                row[i] = true;
            } else {
                row[i] = false;
            }
        }
        return row;
    }

    private static boolean isHeaderLine(String line){
        String[] split = line.split(",");
        for (int i = 0; i < split.length; i++){
            split[i] = split[i].trim();
        }
        final int ZERO_ONE = 1, T_F = 2, TRUE_FALSE = 3;
        int type = 0;
        for (int i = 0; i < split.length; i++){
            if (split[i].length() > 0) {
                if (type == 0) {
                    if (split[i].equalsIgnoreCase("T") || split[i].equalsIgnoreCase("F")){
                        type = T_F;
                    } else if (split[i].equalsIgnoreCase("true") || split[i].equalsIgnoreCase("false")){
                        type = TRUE_FALSE;
                    } else if (split[i].equalsIgnoreCase("0") || split[i].equalsIgnoreCase("1")){
                        type = ZERO_ONE;
                    } else {
                        return true;
                    }
                } else {
                    if (type == ZERO_ONE){
                        if (!split[i].equalsIgnoreCase("0") && !split[i].equalsIgnoreCase("1")){
                            return true;
                        }
                    } else if (type == T_F){
                        if (!split[i].equalsIgnoreCase("t") && !split[i].equalsIgnoreCase("f")){
                            return true;
                        }
                    } else if (type == TRUE_FALSE){
                        if (!split[i].equalsIgnoreCase("true") && !split[i].equalsIgnoreCase("false")){
                            return true;
                        }
                    }
                }
            }
        }
        return false;
    }

    public Pair<BinaryDataset,BinaryDataset> randomSplit(double fraction, Random random){
        int[] indexes = VectorUtils.sequence(0, this.dataset.length-1);
        VectorUtils.shuffle(indexes, random);
        boolean[][] datasetA = new boolean[(int)Math.ceil(dataset.length*fraction)][];
        double[] weightsA = new double[datasetA.length];
        boolean[][] datasetB = new boolean[this.dataset.length-datasetA.length][];
        double[] weightsB = new double[datasetB.length];
        for (int i = 0; i < datasetA.length; i++){
            datasetA[i] = this.dataset[indexes[i]];
            weightsA[i] = this.weights[indexes[i]];
        }
        for (int i = 0; i < datasetB.length; i++){
            datasetB[i] = this.dataset[indexes[datasetA.length+i]];
            weightsB[i] = this.weights[indexes[datasetA.length+i]];
        }
        return new Pair<BinaryDataset,BinaryDataset>(
                new BinaryDataset(datasetA, this.attributeNames, weightsA),
                new BinaryDataset(datasetB, this.attributeNames, weightsB));
    }

    public boolean[] example(int index){
        return this.dataset[index];
    }

    public Set<Literal> exampleAsSetOfLiterals(int index){
        Set<Literal> retVal = new HashSet<Literal>();
        boolean[] example = this.example(index);
        for (int i = 0; i < example.length; i++){
            retVal.add(new Literal(this.attributeNames[i], !example[i]));
        }
        return retVal;
    }

    public static BinaryDataset merge(BinaryDataset... datasets){
        int numExamples = 0;
        for (BinaryDataset dataset : datasets){
            numExamples += dataset.numExamples();
        }
        boolean[][] data = new boolean[numExamples][];
        double[] weights = new double[numExamples];
        String[] attributes = null;
        int index = 0;
        for (BinaryDataset dataset : datasets){
            if (attributes == null){
                attributes = dataset.attributes();
            } else if (!Arrays.equals(attributes, dataset.attributes())){
                throw new IllegalArgumentException("Merged datasets must have the same attribute lists (including order of the attributes).");
            }
            System.arraycopy(dataset.examples(), 0, data, index, (int)dataset.numExamples());
            System.arraycopy(dataset.weights(), 0, weights, index, (int)dataset.numExamples());
            index += dataset.numExamples();
        }
        return new BinaryDataset(data, attributes, weights);
    }

    public double weight(int index){
        return this.weights[index];
    }

    public double[] weights(){
        return this.weights;
    }

    public boolean[][] examples(){
        return this.dataset;
    }

    public BinaryDataset copy(){
        return new BinaryDataset(this.dataset, this.attributeNames, this.weights);
    }

    public boolean[] attributeValues(String attributeName){
        return this.attributeValues(this.attributesToIndices.get(attributeName));
    }

    public boolean[] attributeValues(int attributeIndex){
        boolean[] retVal = new boolean[(int)this.numExamples()];
        int i = 0;
        for (boolean[] row : this.dataset){
            retVal[i] = row[attributeIndex];
            i++;
        }
        return retVal;
    }

    public BinaryDataset neighbourhood(boolean[] center, int radius){
        List<boolean[]> list = new ArrayList<boolean[]>();
        List<Double> weights = new ArrayList<Double>();
        for (int i = 0; i < this.dataset.length; i++){
            if (VectorUtils.hammingDistance(center, this.dataset[i]) <= radius){
                list.add(this.dataset[i]);
                weights.add(this.weights[i]);
            }
        }
        boolean[][] data = new boolean[list.size()][];
        double[] w = new double[list.size()];
        for (int i = 0; i < list.size(); i++){
            data[i] = list.get(i);
            w[i] = weights.get(i);
        }
        return new BinaryDataset(data, this.attributes(), w);
    }

}
