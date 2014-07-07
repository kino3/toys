package jp.naist.is.shuji_k.calc.interpreter;

import jp.naist.is.shuji_k.calc.exception.CalculatorException;
import jp.naist.is.shuji_k.calc.tree.ParseTreeNode;

public abstract class AbstractInterpreter {
    public abstract Object interpret(ParseTreeNode tree) throws CalculatorException;

}
