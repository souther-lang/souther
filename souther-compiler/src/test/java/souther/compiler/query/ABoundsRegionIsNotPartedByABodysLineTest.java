package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.BorderObligationPoint;
import souther.compiler.partition.OwedPoint;
import souther.compiler.partition.PointAnswer;
import souther.compiler.partition.PointAttribution;
import souther.compiler.partition.PointRole;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a clause of a declaration owes away from its line is the region the rules leave, and a body
 * comparing the value inside that region does not part it.
 *
 * <p>{@code fail} counts {@code Failures} up to its own line at three; {@code greet} never reads the
 * count. Both carry the type, and the clause's region beside each of its two lines is one question
 * about {@code Failures} whichever of them reads it — so a row {@code fail} is written in it settles
 * it, and adding {@code greet} neither adds a debt nor holds one open. Parted by {@code fail}'s line,
 * the region above the floor would be owed to {@code fail}'s comparison there and to the declaration
 * only at {@code greet}, and the region below the cap would be the value three alone, which the
 * cap's own point holds, and owed nowhere.
 */
class ABoundsRegionIsNotPartedByABodysLineTest {

    private static final String GREET = """
            behavior greet : (account: Account) -> String

            let greet (account) = account.name

            example greet
                | "greets" : (Account { failures = Failures(0), name = "a" }) -> "a"
            """;

    private static final String FAIL = """
            behavior fail : (account: Account) -> Account
                constructs Account, Failures

            let fail (account) =
                if account.failures.value >= 3 then account
                else Account { ...account, failures = Failures(account.failures.value + 1) }

            example fail
                | "0 to 1" : (Account { failures = Failures(0), name = "a" }) -> Account { failures = Failures(1), name = "a" }
                | "1 to 2" : (Account { failures = Failures(1), name = "a" }) -> Account { failures = Failures(2), name = "a" }
                | "2 to 3" : (Account { failures = Failures(2), name = "a" }) -> Account { failures = Failures(3), name = "a" }
                | "3 stays" : (Account { failures = Failures(3), name = "a" }) -> Account { failures = Failures(3), name = "a" }
            """;

    private static final String HEAD = """
            module example.counted

            data Failures = Int
                invariant value >= 0 && value <= 3
            data Account = { failures: Failures, name: String }

            """;

    private static final String FAIL_ONLY = HEAD + FAIL;
    private static final String BOTH = HEAD + GREET + "\n" + FAIL;
    private static final String BOTH_THE_OTHER_WAY = HEAD + FAIL + "\n" + GREET;

    /**
     * Each line of the clause owes a row at it and a row in the region beside it, and the rows
     * {@code fail} is written meet all four.
     */
    @Test
    void theClauseOwesItsRegionBesideEachLineAndFailsRowsMeetIt() {
        assertEquals(List.of(
                        "ON value = 0 met",
                        "IN value in 0 < value <= 3 met",
                        "ON value = 3 met",
                        "IN value in 0 <= value < 3 met"),
                accountOf(FAIL_ONLY));
    }

    /** A behavior that does not read the count changes nothing about what the clause is owed. */
    @Test
    void aBehaviorThatNeverReadsTheCountChangesNothingTheClauseIsOwed() {
        List<String> alone = accountOf(FAIL_ONLY);
        assertEquals(alone, accountOf(BOTH));
        assertEquals(alone, accountOf(BOTH_THE_OTHER_WAY),
                "and which of the two is written first is no part of it");
    }

    /**
     * The two behaviors are owed one point beside each line, owed to the declaration.
     *
     * <p>The identity and not the verdict. Two readings of one clause folded as two points can still
     * both be met — {@code greet}'s row at nought stands in the region below the cap — so the
     * account above says nothing about whether a reading would have been counted at the other.
     */
    @Test
    void bothBehaviorsReadOnePointBesideEachLine() {
        Map<String, List<BorderAssessment>> byBehavior = readingsOf(BOTH);
        for (String line : List.of("account.failures = 0", "account.failures = 3")) {
            List<OwedPoint> atGreet = owedBesideTheLine(byBehavior.get("greet"), line);
            List<OwedPoint> atFail = owedBesideTheLine(byBehavior.get("fail"), line);
            assertEquals(1, atGreet.size(), () -> line + " at greet: " + atGreet);
            assertEquals(atGreet, atFail, () -> "one point beside " + line);
            assertTrue(atFail.getFirst().attribution() instanceof PointAttribution.TheDeclarations,
                    () -> "owed to Failures: " + atFail);
        }
    }

    /**
     * {@code fail}'s own line still owes its rows to {@code fail}.
     *
     * <p>What the clause no longer reads is measured where it is drawn: the run below three is owed
     * on the account of the comparison that stops it.
     */
    @Test
    void theBodysOwnLineIsStillOwedToTheBody() {
        BorderAssessment comparison = readingsOf(FAIL_ONLY).get("fail").stream()
                .filter(each -> !each.border().owes().isEmpty()
                        && each.border().owes().stream().allMatch(point -> point.attribution()
                                instanceof PointAttribution.TheReading))
                .findFirst()
                .orElseThrow(() -> new AssertionError("fail's comparison owes fail its rows"));
        assertTrue(comparison.border().answer(PointRole.OUT) instanceof PointAnswer.InRegion,
                () -> "the run below its line is owed a row: " + comparison.border());
    }

    /** What became of each point the module's declarations are owed, as role, said and met. */
    private static List<String> accountOf(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Adequacy.DeclaredBoundaries account =
                compilation.db().ask(new Adequacy.DeclaredBorders("example.counted")).value();
        assertNotNull(account, "the model under test compiles");
        return account.owed().stream()
                .map(each -> each.debt().role() + " " + each.said() + " "
                        + (each.debt().owed().hasRowWitness() ? "met" : "unmet"))
                .toList();
    }

    private static Map<String, List<BorderAssessment>> readingsOf(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, List<BorderAssessment>> boundaries =
                Adequacy.boundariesOf(compilation.db(), "example.counted");
        assertNotNull(boundaries, "the model under test compiles");
        return boundaries;
    }

    /** The points a reading of the clause's line at {@code line} owes away from it. */
    private static List<OwedPoint> owedBesideTheLine(List<BorderAssessment> readings, String line) {
        return readings.stream()
                .filter(each -> each.label().equals(line)
                        && each.border().owes().stream().noneMatch(point -> point.attribution()
                                instanceof PointAttribution.TheReading))
                .flatMap(each -> each.border().owes().stream())
                .filter(point -> point.point() instanceof BorderObligationPoint.InRegion)
                .toList();
    }
}
