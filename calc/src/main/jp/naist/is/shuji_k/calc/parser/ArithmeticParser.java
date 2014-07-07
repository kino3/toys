package jp.naist.is.shuji_k.calc.parser;

import static jp.naist.is.shuji_k.calc.ArithmeticCalculator.DIVIDE;
import static jp.naist.is.shuji_k.calc.ArithmeticCalculator.LEFT_PAREN;
import static jp.naist.is.shuji_k.calc.ArithmeticCalculator.MINUS;
import static jp.naist.is.shuji_k.calc.ArithmeticCalculator.MULTIPLY;
import static jp.naist.is.shuji_k.calc.ArithmeticCalculator.PLUS;
import static jp.naist.is.shuji_k.calc.ArithmeticCalculator.RIGHT_PAREN;

import java.util.List;

import jp.naist.is.shuji_k.calc.exception.CalculatorException;
import jp.naist.is.shuji_k.calc.tree.ParseTreeBranchNode;
import jp.naist.is.shuji_k.calc.tree.ParseTreeLeafNode;
import jp.naist.is.shuji_k.calc.tree.ParseTreeNode;

/**
 * 四則演算の式を読み取って構文木を作成するパーサです
 *
 * @author Kinoshita Shuji
 *
 */
public class ArithmeticParser extends AbstractParser {

    // TODO 仕様としてこれとtokenの正規表現をまとめる。
    // expr -> expr + term | expr - term | term
    // term -> term * factor | term / factor | factor
    // factor -> number | ( expr )
    // という文法を表現すればよい

    /**
     * コンストラクタ
     *
     * @param list
     */
    public ArithmeticParser(List<Object> list) {
        this.tokenList = list;
        setMaxPos(list);
        next();
    }

    /*
     * (非 Javadoc)
     *
     * @see jp.naist.is.shuji_k.calc.parser.AbstractParser#parse()
     */
    @Override
    public ParseTreeNode parse() throws CalculatorException {
        return expression();
    }

    /**
     * 非終端記号exprの文法を実装しています<br/>
     * expr -> expr + term | expr - term | term
     *
     * @return
     * @throws CalculatorException
     */
    private ParseTreeNode expression() throws CalculatorException {
        ParseTreeNode node = term();
        while (true) {
            if (hasNext() == false) {
                return node;
            }

            if (nextToken.equals(RIGHT_PAREN)) {
                //TODO backはなくてもいけるはず。あったらまずいのでは？
                return node;
            }

            if (nextToken.equals(PLUS)) {
                next();
                node = new ParseTreeBranchNode(PLUS, node, term());
            } else if (nextToken.equals(MINUS)) {
                next();
                node = new ParseTreeBranchNode(MINUS, node, term());
            }

        }

    }

    /**
     * 非終端記号termの文法を実装しています<br/>
     * term -> term * factor | term / factor | factor
     *
     * @return
     * @throws CalculatorException
     */
    private ParseTreeNode term() throws CalculatorException {
        ParseTreeNode node = factor();

        while (true) {
            if (hasNext() == false) {
                return node;
            }

            if (nextToken.equals(RIGHT_PAREN) || nextToken.equals(PLUS) || nextToken.equals(MINUS)) {
                //TODO backはなくてもいけるはず。あったらまずいのでは？
                return node;
            }

            if (nextToken.equals(MULTIPLY)) {
                next();
                node = new ParseTreeBranchNode(MULTIPLY, node, factor());
            } else if (nextToken.equals(DIVIDE)) {
                next();
                node = new ParseTreeBranchNode(DIVIDE, node, factor());
            } else {
                throw new CalculatorException();
            }
        }

    }

    /**
     * 非終端記号factorの文法を実装しています。<br/>
     * factor -> digit | ( expr )
     *
     * @return
     * @throws CalculatorException
     */
    private ParseTreeNode factor() throws CalculatorException {
        ParseTreeNode node;
        //TODO ここでnextしないでも書けるはず。nextTokenは外に出すほうが自然か
        //TODO 自分が処理するstringをもらう、という形式はどうか。prefixを返す

        if (nextToken.equals(LEFT_PAREN)) {
            next();
            node = expression();
            if (nextToken.equals(RIGHT_PAREN)) {
                next();
                return node;
            } else {
                throw new CalculatorException();
            }
        } else if (nextToken instanceof Integer) {
            node = new ParseTreeLeafNode((Integer) nextToken);
            next();
            return node;
        } else {
            throw new CalculatorException();
        }

    }

}
