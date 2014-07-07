package jp.naist.is.shuji_k.calc;

import static org.hamcrest.CoreMatchers.is;
import static org.junit.Assert.*;
import jp.naist.is.shuji_k.calc.Calculator;
import jp.naist.is.shuji_k.calc.exception.CalculatorException;

import org.junit.Test;

public class ArithmeticCalculatorTest {

    Calculator calc = new ArithmeticCalculator();

    /**
     * 計算テストクラス
     * @throws CalculatorException
     */
    @Test
    public void testCalc() throws CalculatorException {
        assertThat(test("5+8"), is(13));
        assertThat(test("5-8"), is(-3));
        assertThat(test("(5*8)"), is(40));
        assertThat(test("10/2"), is(5));
        assertThat(test("20+5*4"), is(40));
        assertThat(test("(2+(4+5*4))/(10-8)"), is(13));
    }

    private Integer test(String input) throws CalculatorException {
        char[] inputChars = input.toCharArray();
        return (Integer) calc.calc(inputChars);

    }

}
