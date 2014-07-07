package jp.naist.is.shuji_k.calc.Tokenizer;

import static org.hamcrest.CoreMatchers.instanceOf;
import static org.hamcrest.CoreMatchers.is;
import static org.junit.Assert.assertThat;

import java.util.ArrayList;
import java.util.List;

import jp.naist.is.shuji_k.calc.exception.NestException;
import jp.naist.is.shuji_k.calc.exception.TokenizerException;
import jp.naist.is.shuji_k.calc.tokenizer.ArithmeticTokenizer;

import org.junit.Test;

public class ArithmeticTokenizerTest {

    @Test
    public void testTokenize() throws TokenizerException {
        assertThat(test("3+5"),        is(array(3, "+", 5)));
        assertThat(test("34+56"),      is(array(34, "+", 56)));
        assertThat(test("3+5*6"),      is(array(3, "+", 5, "*", 6)));
        assertThat(test("(3+5)*6"),    is(array("(", 3, "+", 5, ")", "*", 6)));
        assertThat(test("((3+5)*69)"), is(array("(", "(", 3, "+", 5, ")", "*", 69, ")")));

        try {
            test("((3+5)*69");
        } catch (Exception e) {
            assertThat(e, instanceOf(NestException.class));
        }

        try {
            test("(2+)3+5(*69)");
        } catch (Exception e) {
            // Nestのエラーではなく、tokenのエラーとして出る
            assertThat(e, instanceOf(Exception.class));
        }

        try {
            test("((3++5)*69");
        } catch (Exception e) {
            assertThat(e, instanceOf(TokenizerException.class));
        }

    }

    private List<Object> test(String string) throws TokenizerException {
        ArithmeticTokenizer at = new ArithmeticTokenizer();
        return at.tokenize(string.toCharArray());
    }

    private List<Object> array(Object... objects) {
        List<Object> list = new ArrayList<Object>();

        for (Object obj : objects) {
            list.add(obj);
        }

        return list;
    }

}
