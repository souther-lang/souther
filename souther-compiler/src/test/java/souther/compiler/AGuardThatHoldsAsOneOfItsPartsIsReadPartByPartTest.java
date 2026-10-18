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
     * Taking a choice apart says what follows from its parts and not what its author named. A
     * string an operation answered is read against a clause only where a guard on the path has
     * said something of it, and a choice names the two parts it joins and nothing written inside
     * them. So a clause over a value only a comparison inside one part names is left to the
     * run-time check, here where the choice is taken apart for the share as everywhere else; were
     * the ways to name what their comparisons compare, the clause would be asked only because
     * something took the choice apart, and the part leaving the value it refuses would make this
     * a construction that may abort.
     *
     * <p>The control names the value in a conjunction, which names both of its halves, and the
     * value the guard leaves is the one the clause refuses.
     */
    @Test
    void aValueOnlyAComparisonInsideAPartNamesIsNotNamedByTakingTheChoiceApart() {
        String model = """
                module demo

                data Labelled = { q: Int, s: String }
                    invariant q >= 0 - 50 && q <= 50
                    invariant s /= "pos"

                behavior label : (among: Int, name: String) -> Labelled
                    constructs Labelled

                let label (among, name) = {
                    guard %s else Labelled { q = 0, s = "none" }
                    Labelled { q = Rational.toInt(DOWN, 100 / among), s = String.trim(name) }
                }
                """;
        assertEquals(List.of(), judged(model.formatted(
                "(among >= 2 && String.trim(name) == \"pos\")"
                        + " || (among <= 0 - 2 && String.trim(name) == \"neg\")")));
        assertEquals(List.of("E2010"), judged(model.formatted(
                "among >= 2 && String.trim(name) == \"pos\"")));
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

    /** And what is written after it is written after nothing: a run never gets past a value it
     * never builds, so a construction there that every value fails is never reached either. */
    @Test
    void whatFollowsAConstructionNoPartLeadsToIsNotReached() {
        String before = String.join("\n    ",
                "guard amount >= 0 && amount <= 100 else Share(1000)",
                "guard among >= 2 || among <= 0 - 2 else Share(1000)",
                "guard among >= 0 - 1 && among <= 1 else Share(1000)",
                "let first = Share(Rational.toInt(DOWN, amount / among))");
        assertEquals(List.of(), judged(shares("value >= 1000", before
                + "\n    Share(amount - 1000)")));
        assertEquals(List.of("E2010"), judged(shares("value >= 1000",
                "guard amount >= 0 && amount <= 100 else Share(1000)\n    Share(amount - 1000)")));
    }

    /**
     * A choice about a value the construction does not read is passed over and costs no copy, so
     * however many stand before the one that matters, that one is still taken apart. Without the
     * passing over, the eight before it would have taken every copy the walk may make.
     */
    @Test
    void aChoiceAboutAValueTheConstructionDoesNotReadIsPassedOver() {
        StringBuilder before = new StringBuilder();
        for (int i = 0; i < 8; i++) {
            before.append("guard tag >= %d || tag <= %d else Share(1)\n    "
                    .formatted(50 + i, 49 + i));
        }
        assertEquals(List.of(), judged("""
                module demo

                data Share = Int
                    invariant value >= 0 - 50 && value <= 50

                behavior apportion : (amount: Int, among: Int, tag: Int) -> Share
                    constructs Share

                let apportion (amount, among, tag) = {
                    %s
                }
                """.formatted(share(before
                + "guard among >= 2 || among <= 0 - 2 else Share(1)"))));
    }

    /**
     * Each way a construction is judged under is a copy of the reading the walk made there, and
     * the copies compound with every choice taken apart that both ways of are entered. Past what
     * the walk may copy, the choices left are not taken apart, and the construction is owed what
     * the whole of them leaves it — not proven over the ways that were read.
     */
    @Test
    void choicesPastWhatTheWalkMayCopyAreNotTakenApart() {
        assertEquals(List.of(), judged(sharedAmong(4)));
        assertEquals(List.of("E2011"), judged(sharedAmong(5)));
    }

    /** A hundred shared {@code count} ways, each among a count a choice of its own keeps out of the
     * hole around nought, and each share bounded by what its own choice says. */
    private static String sharedAmong(int count) {
        List<String> fields = new ArrayList<>();
        List<String> clauses = new ArrayList<>();
        List<String> params = new ArrayList<>();
        List<String> names = new ArrayList<>();
        List<String> nothing = new ArrayList<>();
        List<String> given = new ArrayList<>();
        for (int i = 0; i < count; i++) {
            fields.add("s%d: Int".formatted(i));
            clauses.add("s%1$d >= 0 - 50 && s%1$d <= 50".formatted(i));
            params.add("n%d: Int".formatted(i));
            names.add("n%d".formatted(i));
            nothing.add("s%d = 0".formatted(i));
            given.add("s%1$d = Rational.toInt(DOWN, 100 / n%1$d)".formatted(i));
        }
        String none = "Shares { " + String.join(", ", nothing) + " }";
        List<String> guards = new ArrayList<>();
        for (String n : names) {
            guards.add("guard %1$s >= 2 || %1$s <= 0 - 2 else %2$s".formatted(n, none));
        }
        return """
                module demo

                data Shares = { %s }
                    invariant %s

                behavior apportion : (%s) -> Shares
                    constructs Shares

                let apportion (%s) = {
                    %s
                    Shares { %s }
                }
                """.formatted(String.join(", ", fields), String.join(" && ", clauses),
                String.join(", ", params), String.join(", ", names),
                String.join("\n    ", guards), String.join(", ", given));
    }
}
