package jp.naist.is.shuji_k.calc.interpreter;

import jp.naist.is.shuji_k.calc.exception.CalculatorException;
import jp.naist.is.shuji_k.calc.tree.ParseTreeNode;

public class ArithmeticInterpreter extends AbstractInterpreter {

    @Override
    public Object interpret(ParseTreeNode tree) throws CalculatorException {
        return tree.getValue();
    }

}
