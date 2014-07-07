package jp.naist.is.shuji_k.calc;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;

import jp.naist.is.shuji_k.calc.exception.CalculatorException;

/**
 * 計算プログラムの共通部分
 *
 * @author Kinoshita Shuji
 *
 */
public abstract class Calculator {

    /**
     * 入力された文字列
     * TODO 入力サイズは仮
     */
    protected char[] inputChars;

    /**
     * プログラム実行（共通部分）
     */
    protected void exec() {
        inputChars = inputFormula();

        Object output = new Object();
        try {
            output = calc(inputChars);
        } catch (CalculatorException e) {
            e.printStackTrace();
        }

        System.out.println("Result: " + output);
    }

    protected abstract Object calc(char[] inputChars) throws CalculatorException;

    /**
     * ユーザに入力を求めます。
     * @return 入力された文字列（改行コードはなし）
     */
    protected char[] inputFormula() {
        System.out.println("Please input formula.");

        InputStreamReader isr = new InputStreamReader(System.in);
        BufferedReader reader = new BufferedReader(isr);
        String chars = "";

        try {
            chars = reader.readLine();
        } catch (IOException e) {
            e.printStackTrace();
        }

        return chars.toCharArray();
    }

    /**
     * メインプログラム
     *
     * @param args プログラム引数（特に利用しない）
     */
    public static void main(String[] args) {
        Calculator calc = new ArithmeticCalculator();
        calc.exec();
    }
}
