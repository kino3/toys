package jp.naist.is.shuji_k.calc.tokenizer;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import jp.naist.is.shuji_k.calc.exception.NestException;
import jp.naist.is.shuji_k.calc.exception.TokenizerException;
import static jp.naist.is.shuji_k.calc.tokenizer.ArithmeticTokenizer.TokenState.*;

/**
 * 四則演算用トークン作成器
 *
 * @author Kinoshita Shuji
 *
 */
public class ArithmeticTokenizer extends AbstractTokenizer {

    protected static final String REGEX_NUMBERS = "[0-9]";
    protected static final String REGEX_OPERATORS = "[+-/*]";
    protected static final String REGEX_LEFTPAREN = "[(]";
    protected static final String REGEX_RIGHTPAREN = "[)]";

    public static enum TokenState{
        BEGIN, NUMBER, OPERATOR, LEFTPAREN, RIGHTPAREN, END;
    }

    protected List<Object> tokenList = new ArrayList<Object>();


    /**
     * キーが現在の文字、値が次にとることができる文字。ここにない組み合わせはエラーとする。
     */
    protected static final HashMap<TokenState, TokenState[]> tokenMap = new HashMap<TokenState, TokenState[]>() {
        private static final long serialVersionUID = 1L;
        {
            put(BEGIN,      new TokenState[]{NUMBER, LEFTPAREN});
            put(NUMBER,     new TokenState[]{NUMBER, OPERATOR, RIGHTPAREN});
            put(OPERATOR,   new TokenState[]{NUMBER, LEFTPAREN});
            put(LEFTPAREN,  new TokenState[]{NUMBER, LEFTPAREN});
            put(RIGHTPAREN, new TokenState[]{OPERATOR, RIGHTPAREN});//乗算×の省略は考えないのでLeftparenは除外
        }
    };

    /* (非 Javadoc)
     * @see jp.naist.is.shuji_k.calc.tokenizer.AbstractTokenizer#tokenize(char[])
     */
    @Override
    public List<Object> tokenize(char[] inputs) throws TokenizerException {
        // java付属のStreamTokenizerを使わない。練習のため。

        TokenState state = BEGIN;
        StringBuffer numberBuf = new StringBuffer();
        int nest = 0;

        for (char c : inputs) {
            TokenState nextState = getNextState(c, state);

            switch (nextState) {
            case NUMBER:
                numberBuf.append(c);
                break;
            case OPERATOR:
                numberBuf = addNumberToList(numberBuf);
                tokenList.add(String.valueOf(c));
                break;
            case LEFTPAREN:
                tokenList.add(String.valueOf(c));
                nest++;
                break;
            case RIGHTPAREN:
                numberBuf = addNumberToList(numberBuf);
                tokenList.add(String.valueOf(c));
                nest--;
                break;
            default:
                break;
            }
            state = nextState;
        }
        // 最後の数値がまだListに追加されていないことに注意する
        numberBuf = addNumberToList(numberBuf);

        if ( nest != 0 ){
            //TODO ここではわからないはず、())(をテストしてみる。→(()(はtokenize失敗のexceptionが出る。
            // tokenizeの部分で書くのがそもそも変、ということだが、あっても悪いことはないので残す。
            throw new NestException();
        }

        return tokenList;
    }

    protected StringBuffer addNumberToList(StringBuffer numberBuf) {
        if (numberBuf.length() != 0) {
            tokenList.add(Integer.valueOf(numberBuf.toString()));
            numberBuf = new StringBuffer();
        }
        return numberBuf;
    }

    protected static TokenState getNextState(char c, TokenState before) throws TokenizerException {
        TokenState after = null;
        if (matches(c, REGEX_NUMBERS)) {
            after = NUMBER;
        } else if (matches(c, REGEX_OPERATORS)) {
            after = OPERATOR;
        } else if (matches(c, REGEX_LEFTPAREN)) {
            after = LEFTPAREN;
        } else if (matches(c, REGEX_RIGHTPAREN)) {
            after = RIGHTPAREN;
        } else if (c == '\n' || c == '\r') {
            return END;
        } else {
            throw new TokenizerException(before, c);
        }

        boolean isCorrectToken = false;
        TokenState[] states = tokenMap.get(before);
        for (TokenState state : states) {
            if (state == after) {
                isCorrectToken = true;
                break;
            }
        }
        if (!isCorrectToken) {
            throw new TokenizerException(before, c);
        }

        return after;
    }

}
