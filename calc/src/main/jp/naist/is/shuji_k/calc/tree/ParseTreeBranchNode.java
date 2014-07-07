package jp.naist.is.shuji_k.calc.tree;

import static jp.naist.is.shuji_k.calc.ArithmeticCalculator.DIVIDE;
import static jp.naist.is.shuji_k.calc.ArithmeticCalculator.MINUS;
import static jp.naist.is.shuji_k.calc.ArithmeticCalculator.MULTIPLY;
import static jp.naist.is.shuji_k.calc.ArithmeticCalculator.PLUS;
import jp.naist.is.shuji_k.calc.exception.CalculatorException;

/**
 * 木構造を表現するノードのうち、枝になるもの<br/>
 * 子のノード２つと演算子を保持します
 *
 * @author Kinoshita Shuji
 *
 */
public class ParseTreeBranchNode extends ParseTreeNode {

    public String operator;
    public ParseTreeNode child1;
    public ParseTreeNode child2;

    public ParseTreeBranchNode(String ope, ParseTreeNode c1, ParseTreeNode c2) {
        this.operator = ope;
        this.child1 = c1;
        this.child2 = c2;
    }

    @Override
    public Integer getValue() throws CalculatorException {
        Integer retValue = null;

        if (this.operator.equals(PLUS)) {
            retValue = child1.getValue() + child2.getValue();
        } else if (this.operator.equals(MINUS)) {
            retValue = child1.getValue() - child2.getValue();
        } else if (this.operator.equals(MULTIPLY)) {
            retValue = child1.getValue() * child2.getValue();
        } else if (this.operator.equals(DIVIDE)) {
            retValue = child1.getValue() / child2.getValue();
        } else {
            throw new CalculatorException();
        }

        return retValue;

    }
}
