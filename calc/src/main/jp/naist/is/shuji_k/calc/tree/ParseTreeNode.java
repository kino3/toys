package jp.naist.is.shuji_k.calc.tree;

import jp.naist.is.shuji_k.calc.exception.CalculatorException;

/**
 * 木構造を表現するクラス
 *
 * @author Kinoshita Shuji
 *
 */
public abstract class ParseTreeNode {

    /**
     * 自身より下のノードの値をすべて計算して取得します。
     * @return
     * @throws CalculatorException
     */
    public abstract Integer getValue() throws CalculatorException;
}
