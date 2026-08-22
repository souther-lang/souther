package souther.compiler;

import java.util.List;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.Diagnostic;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What a {@code guard} states as a relation between two values reaches a construction inside a
 * helper, as what it states of one value on its own already did.
 *
 * <p>The argument is bound to the parameter and the parameter is read through to it, so a rule the
 * helper's body writes about one position becomes a rule about however many positions the argument
 * has. Every fact about it then has to survive that: {@code 額 >= 0} where {@code 額} is a place is
 * one position's range, and the same fact where {@code 額} is {@code 合計金額(投入) - 値段} is a
 * relation the two positions only hold together. The second was dropped, so a construction the check
 * discharged under one spelling of the argument it reported under the other.
 *
 * <p>The helper boundary is where it showed and not what caused it — see
 * {@code ARulesRestIsBoundedByRelationsAndNotOnlyByEndsTest}, which is the same loss with no helper
 * in it. This is here because a construction moved into a helper is what the boundary is for, and
 * because the model the report came from is this one.
 */
class AGuardsRelationReachesAConstructionMovedIntoAHelperTest {

    /**
     * The model the report came from, cut to one denomination.
     *
     * <p>{@code 使える枚数} answers at most what it is handed, and {@code 釣り銭を組む} builds two counts
     * out of that answer — one of them, one of what is left of the pool. Both are owed
     * {@code value >= 0}, and what discharges them is the {@code if} relating the amount to ten
     * times the count, taken with whatever the caller established about the amount.
     */
    private static String model(String guard, String amount) {
        return """
                module demo

                data 硬貨枚数 = Int
                    invariant value >= 0

                data 硬貨束 = { 十円玉: 硬貨枚数 }

                data 組めた = { 内訳: 硬貨束, 残り: 硬貨束 }
                data 組めない
                data 釣り銭の組み方 = 組めた | 組めない

                let 商 (a: Int, b: Int): Int =
                    match Int.divide(a, b) with
                        | Int as n -> n
                        | DivisionByZero -> unreachable "額面は定数で、0になることはない"

                let 使える枚数 (残額: Int, 額面: Int, 手持ち: Int): Int = {
                    let 必要 = 商(残額, 額面)
                    if 必要 < 手持ち then 必要 else 手持ち
                }

                let 合計金額 (束: 硬貨束): Int = 束.十円玉.value * 10

                let 釣り銭を組む (額: Int, プール: 硬貨束): 釣り銭の組み方 = {
                    let 十 = 使える枚数(額, 10, プール.十円玉.value)
                    if 額 - 十 * 10 == 0
                        then 組めた
                            { 内訳 = 硬貨束 { 十円玉 = 硬貨枚数(十) }
                            , 残り = 硬貨束 { 十円玉 = 硬貨枚数(プール.十円玉.value - 十) }
                            }
                        else 組めない
                }

                behavior 買う : (投入: 硬貨束, ストック: 硬貨束, 値段: Int) -> 釣り銭の組み方
                    constructs 組めた, 硬貨束, 硬貨枚数

                let 買う (投入, ストック, 値段) = {
                    guard %s else 組めない
                    釣り銭を組む(%s, ストック)
                }
                """.formatted(guard, amount);
    }

    private static List<String> reported(String guard, String amount) {
        return Compiler.compileWithWarnings(model(guard, amount)).warnings().stream()
                .map(Diagnostic::code)
                .toList();
    }

    /** The argument the report was about: a value the guard bounds only by relating it to another. */
    @Test
    void aRelationalGuardOverTheArgumentDischargesTheConstruction() {
        assertEquals(List.of(),
                reported("合計金額(投入) >= 値段", "合計金額(投入) - 値段"));
    }

    /**
     * The same fact stated of the argument itself rather than of what it was built from.
     *
     * <p>One value and two writings of it, so the two say the same thing about the same construction
     * — and this one was reported while the one above was not, which is a name deciding what may be
     * said of an expression.
     */
    @Test
    void theSameRelationStatedOfTheArgumentItselfDischargesItToo() {
        assertEquals(List.of(),
                reported("合計金額(投入) - 値段 >= 0", "合計金額(投入) - 値段"));
    }

    /** Two places rather than a computed value, which is the same relation with nothing computed
     *  anywhere in it. */
    @Test
    void aRelationBetweenTwoPlacesDischargesItAsWell() {
        assertEquals(List.of(),
                reported("値段 >= 0 && 合計金額(投入) >= 値段", "合計金額(投入) - 値段"));
    }

    /**
     * The control, and the reason the rest of them mean anything.
     *
     * <p>Nothing establishes where the amount lies, so ten times the count is a sum the rules leave
     * running either way and the count may be below nought. A warning here is the check working.
     */
    @Test
    void withNothingEstablishedAboutTheAmountItIsStillReported() {
        assertEquals(List.of("E2011"), reported("値段 >= 0", "値段 - 合計金額(投入)"));
    }
}
