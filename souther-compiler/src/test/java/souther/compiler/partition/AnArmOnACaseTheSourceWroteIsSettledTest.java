package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.AdequacyUncertainty;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * An arm of a {@code match} on a value the source wrote is taken by every row or by none.
 *
 * <p>A helper handed a case written at the call matches what it was handed, and which arm that
 * takes is settled before any row is written: there is no position under the {@code match} for a
 * row to put a case at, and none is needed. Read as a narrowing of a position, the arm is one this
 * reading cannot read, and every rule through it is held open on that. Written with the helper or
 * with what the arm it takes says, a model says the same thing, so the two are held to each other.
 */
class AnArmOnACaseTheSourceWroteIsSettledTest {

    private static final String TRIP = """
            data Trip = { cost: Int, abroad: Bool }
            data Reason = High | Abroad

            let applies (t: Trip, r: Reason): Bool =
                match r with
                    | High -> t.cost >= 100
                    | Abroad -> t.abroad

            behavior submit : (t: Trip) -> Int
            """;

    private static final String ROWS = """

            example submit
                | "cheap and home" : (Trip { cost = 99, abroad = false }) -> 1
                | "expensive" : (Trip { cost = 100, abroad = false }) -> 2
                | "abroad" : (Trip { cost = 99, abroad = true }) -> 2
                | "both" : (Trip { cost = 100, abroad = true }) -> 2
            """;

    @Test
    void aHelperHandedACaseIsReadAsTheArmItTakes() {
        Compilation helper = compiled(TRIP + """
                let submit (t) = if applies(t, High) || applies(t, Abroad) then 2 else 1
                """ + ROWS);
        Compilation written = compiled(TRIP + """
                let submit (t) = if t.cost >= 100 || t.abroad then 2 else 1
                """ + ROWS);
        assertEquals(List.of(), open(helper), "nothing holds the verdict open");
        assertEquals(AdequacyReport.of(written).adequacy(), AdequacyReport.of(helper).adequacy());
    }

    /** And one call alone, whose other arm no row takes. */
    @Test
    void anArmNoRowTakesIsNoDistinction() {
        Compilation helper = compiled(TRIP + """
                let submit (t) = if applies(t, Abroad) then 2 else 1
                """ + """

                example submit
                    | "home" : (Trip { cost = 1, abroad = false }) -> 1
                    | "abroad" : (Trip { cost = 1, abroad = true }) -> 2
                """);
        assertEquals(List.of(), open(helper), "nothing holds the verdict open");
        assertEquals(AdequacyReport.AdequacyStatus.SATISFIED, AdequacyReport.of(helper).adequacy());
    }

    /**
     * An arm one call never takes and another does is no dead branch.
     *
     * <p>The helper is the author's and so is each arm of it. Each call leaves the other arm
     * unreachable, and the author is told to take out neither: one of the calls needs it.
     */
    @Test
    void anArmAnotherCallTakesIsNotDead() {
        assertEquals(List.of(), deadBranches(compiled(TRIP + """
                let submit (t) = if applies(t, High) || applies(t, Abroad) then 2 else 1
                """ + ROWS)));
    }

    /** And an arm no call takes is, said once at the arm the author wrote. */
    @Test
    void anArmNoCallTakesIsDeadOnce() {
        assertEquals(List.of("E1327"), deadBranches(compiled(TRIP + """
                let submit (t) =
                    if applies(t, Abroad) || (t.cost > 5 && applies(t, Abroad)) then 2 else 1
                """ + """

                example submit
                    | "home" : (Trip { cost = 1, abroad = false }) -> 1
                    | "abroad" : (Trip { cost = 1, abroad = true }) -> 2
                """)));
    }

    private static List<String> deadBranches(Compilation compilation) {
        return compilation.warnings().stream().map(each -> each.diagnostic().code())
                .filter("E1327"::equals).toList();
    }

    private static List<AdequacyUncertainty> open(Compilation compilation) {
        return AdequacyReport.of(compilation).whatKeepsTheVerdictOpen();
    }

    private static Compilation compiled(String model) {
        Compilation compilation = Compilation.ofSource("module demo\n\n" + model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors(), "the model compiles and its rows hold");
        return compilation;
    }
}
