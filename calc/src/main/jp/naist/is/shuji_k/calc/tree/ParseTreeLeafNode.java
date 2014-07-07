package jp.naist.is.shuji_k.calc.tree;

/**
 * 構文木のうち、葉にあたる木。数値が格納されます。
 *
 * @author Kinoshita Shuji
 *
 */
public class ParseTreeLeafNode extends ParseTreeNode {

    protected Integer value;

    public ParseTreeLeafNode(Integer v) {
        this.value = v;
    }

    public Integer getValue(){
        return this.value;
    }
}
