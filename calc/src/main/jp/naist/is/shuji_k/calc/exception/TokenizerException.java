package jp.naist.is.shuji_k.calc.exception;

import jp.naist.is.shuji_k.calc.tokenizer.ArithmeticTokenizer.TokenState;

public class TokenizerException extends CalculatorException {

    TokenState beforeState;

    char currentChar;

    public TokenizerException(){

    }

    public TokenizerException(TokenState before, char c) {
        this.beforeState = before;
        this.currentChar = c;
    }

    @Override
    public String getMessage() {
        return "beforeState:" + this.beforeState.toString() + " currentChar:"
                + currentChar;
    };

    /**
     *
     */
    private static final long serialVersionUID = 1L;

}
