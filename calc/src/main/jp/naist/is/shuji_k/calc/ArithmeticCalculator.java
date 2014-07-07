package jp.naist.is.shuji_k.calc;

import java.util.List;

import jp.naist.is.shuji_k.calc.exception.CalculatorException;
import jp.naist.is.shuji_k.calc.interpreter.ArithmeticInterpreter;
import jp.naist.is.shuji_k.calc.parser.ArithmeticParser;
import jp.naist.is.shuji_k.calc.tokenizer.ArithmeticTokenizer;
import jp.naist.is.shuji_k.calc.tree.ParseTreeNode;

public class ArithmeticCalculator extends Calculator {

    public static final String LEFT_PAREN = "(";
    public static final String RIGHT_PAREN = ")";
    public static final String PLUS = "+";
    public static final String MINUS = "-";
    public static final String MULTIPLY = "*";
    public static final String DIVIDE = "/";

    @Override
    protected Object calc(char[] inputChars) throws CalculatorException{

        // tokenに分解
        ArithmeticTokenizer tokenizer = new ArithmeticTokenizer();
        List<Object> tokenList = tokenizer.tokenize(inputChars);

        // 構文木を作成
        ArithmeticParser parser = new ArithmeticParser(tokenList);
        ParseTreeNode tree = parser.parse();

        // 評価（計算）
        ArithmeticInterpreter interpreter = new ArithmeticInterpreter();
        return interpreter.interpret(tree);
    }
}
