package jp.naist.is.shuji_k.calc.tokenizer;

import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import jp.naist.is.shuji_k.calc.exception.TokenizerException;

public abstract class AbstractTokenizer {
    public abstract List<Object> tokenize(char[] input) throws TokenizerException;

    protected String regex = "";

    /**
     * 該当の文字で構成されているかどうかのチェックをします。
     *
     * @param formula
     * @return
     */
    protected boolean isCorrectLetters(String formula) {
        Pattern pattern = Pattern.compile(regex);
        Matcher matcher = pattern.matcher(formula);
        return matcher.matches();
    }

    /**
     * 該当文字が正規表現で一致していればtrueを返します
     *
     * @param c
     * @param regex
     * @return
     */
    protected static boolean matches(char c, String regex){
        Pattern pattern = Pattern.compile(regex);
        Matcher matcher = pattern.matcher(String.valueOf(c));
        return matcher.matches();
    }
}
