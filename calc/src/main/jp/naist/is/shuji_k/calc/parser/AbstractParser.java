package jp.naist.is.shuji_k.calc.parser;

import java.util.List;

import jp.naist.is.shuji_k.calc.exception.CalculatorException;
import jp.naist.is.shuji_k.calc.tree.ParseTreeNode;

public abstract class AbstractParser {

    protected List<Object> tokenList;

    /**
     * 次のトークン。{@link #next()}で設定される。
     */
    protected Object nextToken;

    /**
     * 現在読んでいるトークンの位置
     */
    private int pos = -1;

    /**
     * 末尾のトークンの位置
     */
    private int maxPos;

    /**
     * トークン位置の最大値を設定します。
     *
     * @param list
     */
    protected void setMaxPos(List<Object> list) {
        this.maxPos = list.size() - 1;
    }

    /**
     * 次のトークンがあればtrueを返します
     *
     * @return
     */
    protected boolean hasNext() {
        return pos < maxPos;
    }

    /**
     * 次のトークンを取得し、カーソルを1つ進めます
     *
     * @return
     */
    protected Object next() {
        if ( hasNext() ){
            pos++;
            nextToken = tokenList.get(pos);
        }
        return nextToken;
    }

    /**
     * カーソルを1つ戻します
     */
    protected void back() {
        pos--;
    }

    public AbstractParser() {
    }

    public abstract ParseTreeNode parse() throws CalculatorException;

}
