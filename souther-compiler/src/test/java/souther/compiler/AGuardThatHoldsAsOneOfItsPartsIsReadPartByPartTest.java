package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A guard that holds as one of its parts is read part by part where a construction is judged.
 *
 * <p>{@code among >= 2 || among <= 0 - 2} leaves {@code among} out of a hole around nought, and no
 * range says that: the range its two parts span holds nought. So a construction the whole of the
 * guard leaves unsettled is judged again under each part taken in alone, and what holds in every
 * part holds there (spec §invariant-discharge). A quotient by a divisor held that way is bounded on
 * each side, which is what the range of the whole could not say for a decimal divisor at all.
 *
 * <p>Each claim left owed has a value that breaks it, and the value is checked rather than named:
 * pinned to it, the construction is refused.
 */
class AGuardThatHoldsAsOneOfItsPartsIsReadPartByPartTest {

    private static String shares(String bounds, String body) {
        return """
                module demo

                data Share = Int
                    invariant %s

                let apart (n) = n >= 2 || n <= 0 - 2

                behavior apportion : (amount: Int, among: Int) -> Share
                    constructs Share

                let apportion (amount, among) = {
                    %s
                }
                """.formatted(bounds, body);
    }

    private static String quotients(String bounds, String guards) {
        return """
                module demo

                data Q = Decimal
                    invariant %s

                behavior divide : (x: Decimal, y: Decimal) -> Q
                    constructs Q

                let divide (x, y) = {
                    %s
                    match Decimal.divide(x, y, 2, HALF_UP) with
                        | Decimal as q -> Q(q)
                        | DivisionByZero -> Q(0m)
                }
                """.formatted(bounds, guards);
    }

    /** What the discharge check said: the warnings, or the refusal it stopped at. */
    private static List<String> judged(String model) {
        try {
            return Compiler.compileWithWarnings(model).warnings().stream()
                    .map(Diagnostic::code)
                    .filter(code -> code.startsWith("E20"))
                    .toList();
        } catch (CompileException refused) {
            return List.of(refused.getMessage().substring(0, 5));
        }
    }

    private static final String AMOUNT = "guard amount >= 0 && amount <= 100 else Share(1)";

    private static String share(String guards) {
        return AMOUNT + "\n    " + guards + "\n    Share(Rational.toInt(DOWN, amount / among))";
    }

    /**
     * A hundred shared among at least two either way is at most fifty either way, and not nearer
     * nought than that: among two it is fifty, and among minus two minus fifty.
     */
    @Test
    void aWholeDivisorKeptOutOfAHoleAroundNoughtBoundsTheShareOnEachSide() {
        String apart = share("guard among >= 2 || among <= 0 - 2 else Share(1)");
        assertEquals(List.of(), judged(shares("value >= 0 - 50 && value <= 50", apart)));
        assertEquals(List.of("E2011"), judged(shares("value >= 0 - 49 && value <= 50", apart)));
        assertEquals(List.of("E2010"), judged(shares("value >= 0 - 49 && value <= 50", """
                guard amount == 100 else Share(1)
                    guard among >= 2 || among <= 0 - 2 else Share(1)
                    guard among == 0 - 2 else Share(1)
                    Share(Rational.toInt(DOWN, amount / among))""")));
        assertEquals(List.of("E2011"), judged(shares("value >= 0 - 50 && value <= 49", apart)));
        assertEquals(List.of("E2010"), judged(shares("value >= 0 - 50 && value <= 49", """
                guard amount == 100 else Share(1)
                    guard among >= 2 || among <= 0 - 2 else Share(1)
                    guard among == 2 else Share(1)
                    Share(Rational.toInt(DOWN, amount / among))""")));
    }

    /**
     * A decimal divisor at least a half from nought either way divides a hundred into at most two
     * hundred either way. Without the hole nothing bounds it, since a decimal other than nought can
     * be nearer nought than any number named.
     */
    @Test
    void aDecimalDivisorKeptOutOfAHoleAroundNoughtBoundsTheQuotient() {
        String apart = """
                guard x >= 0m && x <= 100m else Q(1m)
                    guard y >= 0.5m || y <= 0m - 0.5m else Q(1m)""";
        assertEquals(List.of(), judged(quotients("value >= 0m - 200m && value <= 200m", apart)));
        assertEquals(List.of("E2011"),
                judged(quotients("value >= 0m - 200m && value <= 199m", apart)));
        assertEquals(List.of("E2010"), judged(quotients("value >= 0m - 200m && value <= 199m", """
                guard x == 100m else Q(1m)
                    guard y >= 0.5m || y <= 0m - 0.5m else Q(1m)
                    guard y == 0.5m else Q(1m)""")));
    }

    /** The control: a decimal divisor that is only not nought is in no hole, and each part of the
     * guard is as near nought as anything. */
    @Test
    void aDecimalDivisorThatIsOnlyNotNoughtStatesNothingOnEitherSide() {
        assertEquals(List.of("E2011"), judged(quotients("value >= 0m - 200m && value <= 200m", """
                guard x >= 0m && x <= 100m else Q(1m)
                    guard y > 0m || y < 0m else Q(1m)""")));
    }

    /** One choice written another way is the same choice: its parts in the other order, as the
     * denial of a conjunction, through a helper, as the condition of an {@code if}, and over a name
     * the divisor was given. */
    @Test
    void theSameChoiceWrittenAnotherWayIsReadAlike() {
        String bounds = "value >= 0 - 50 && value <= 50";
        List<String> owed = new ArrayList<>();
        for (String written : List.of(
                share("guard among <= 0 - 2 || among >= 2 else Share(1)"),
                share("guard Bool.not(among < 2 && among > 0 - 2) else Share(1)"),
                share("guard apart(among) else Share(1)"),
                AMOUNT + """

                            if among >= 2 || among <= 0 - 2
                                then Share(Rational.toInt(DOWN, amount / among))
                                else Share(1)""",
                AMOUNT + """

                            let d = among
                            guard d >= 2 || d <= 0 - 2 else Share(1)
                            Share(Rational.toInt(DOWN, amount / d))""")) {
            if (!judged(shares(bounds, written)).isEmpty()) {
                owed.add(written);
            }
        }
        assertEquals(List.of(), owed);
    }

    /**
     * What one part of a choice says of two values is said of both together. Each part keeps the
     * dividend and the divisor on one side of nought, so the quotient is never below nought; taken
     * apart value by value, ten by minus a half is among what is left, and that is minus twenty.
     */
    @Test
    void whatOnePartSaysOfTwoValuesStaysTogether() {
        String bounded = "guard x >= 0m - 100m && x <= 100m else Q(1m)\n    ";
        assertEquals(List.of(), judged(quotients("value >= 0m", bounded
                + "guard (x >= 10m && y >= 0.5m) || (x <= 0m - 10m && y <= 0m - 0.5m) else Q(1m)")));
        String eachOnItsOwn = """
                guard x >= 10m || x <= 0m - 10m else Q(1m)
                    guard y >= 0.5m || y <= 0m - 0.5m else Q(1m)""";
        assertEquals(List.of("E2011"), judged(quotients("value >= 0m", bounded + eachOnItsOwn)));
        assertEquals(List.of("E2010"), judged(quotients("value >= 0m", eachOnItsOwn
                + "\n    guard x == 10m && y == 0m - 0.5m else Q(1m)")));
    }

    /**
     * A construction no part of the choice leads to, under what the path holds further on, is no
     * value built, and nothing is said of it. The control leaves the divisor two either way, and
     * every share there is one the invariant fails.
     */
    @Test
    void aConstructionNoPartLeadsToIsNotJudged() {
        String amount = "guard amount >= 0 && amount <= 100 else Share(1000)";
        String apart = "guard among >= 2 || among <= 0 - 2 else Share(1000)";
        String share = "Share(Rational.toInt(DOWN, amount / among))";
        assertEquals(List.of(), judged(shares("value >= 1000", String.join("\n    ", amount, apart,
                "guard among >= 0 - 1 && among <= 1 else Share(1000)", share))));
        assertEquals(List.of("E2010"), judged(shares("value >= 1000", String.join("\n    ",
                amount, apart, "guard among >= 0 - 2 && among <= 2 else Share(1000)", share))));
    }

    /**
     * Each part a construction is judged under is a copy of the reading the walk made there, and
     * the copies compound with every choice taken apart. Past what the walk may copy, the choices
     * left are not taken apart, and the construction is owed what the whole of them leaves it —
     * not proven over the parts that were read.
     */
    @Test
    void choicesPastWhatTheWalkMayCopyAreNotTakenApart() {
        assertEquals(List.of(), judged(shares("value >= 0 - 50 && value <= 50",
                share(otherChoices(3) + "guard among >= 2 || among <= 0 - 2 else Share(1)"))));
        assertEquals(List.of("E2011"), judged(shares("value >= 0 - 50 && value <= 50",
                share(otherChoices(5) + "guard among >= 2 || among <= 0 - 2 else Share(1)"))));
    }

    /** {@code count} choices about the amount, which the share's bounds do not turn on. */
    private static String otherChoices(int count) {
        StringBuilder out = new StringBuilder();
        for (int i = 0; i < count; i++) {
            out.append("guard amount >= %d || amount <= 0 - %d else Share(1)\n    "
                    .formatted(i, i + 1));
        }
        return out.toString();
    }
}
