package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.coverage.ControlPlace;
import souther.compiler.diag.Note;
import souther.compiler.diag.msg.DeadBranchMessage;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.AdequacyUncertainty;

import java.util.ArrayList;
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

    /**
     * And an arm no call takes is, said once at the arm the author wrote, with the reason every call
     * left it dead by.
     */
    @Test
    void anArmNoCallTakesIsDeadOnce() {
        Compilation compilation = compiled(TRIP + """
                let submit (t) =
                    if applies(t, Abroad) || (t.cost > 5 && applies(t, Abroad)) then 2 else 1
                """ + """

                example submit
                    | "home" : (Trip { cost = 1, abroad = false }) -> 1
                    | "abroad" : (Trip { cost = 1, abroad = true }) -> 2
                """);
        assertEquals(List.of("E1327"), deadBranches(compilation));
        assertEquals(List.of("Abroad is never High"), whyDead(compilation));
    }

    /**
     * An arm every call leaves dead for a reason of its own is dead, and no one call's reason is
     * said of it.
     *
     * <p>One call hands the helper {@code A} and the other {@code B}, so each says the value matched
     * on is only that case — true of the call and false of the arm, which both reach.
     */
    @Test
    void anArmDeadForDifferentReasonsIsSaidDeadWithoutOne() {
        Compilation compilation = compiled("""
                data Pick = A | B | C

                let h (p: Pick): Int =
                    match p with
                        | A -> 1
                        | B -> 2
                        | C -> 3

                behavior g : (n: Int) -> Int
                let g (n) = if n > 5 then h(A) else h(B)

                example g
                    | "big" : (6) -> 1
                    | "small" : (5) -> 2
                """);
        assertEquals(List.of("E1327"), deadBranches(compilation));
        assertEquals(List.of("nothing more"), whyDead(compilation));
    }

    /**
     * An arm on a case that is itself a sum takes the leaves under it.
     *
     * <p>{@code Station} is a {@code OnceKind}, so the helper handed one takes its {@code OnceKind}
     * arm and only its {@code Renkei} arm is dead.
     */
    @Test
    void anArmOnASumOfCasesTakesTheCasesUnderIt() {
        String visit = """
                data Station  = { at: String }
                data Hospital = { at: String }
                data Renkei   = { at: String }
                data OnceKind  = Station | Hospital
                data VisitKind = OnceKind | Renkei

                let fee (k: VisitKind): Int =
                    match k with
                        | OnceKind -> 1
                        | Renkei -> 2

                behavior visit : (n: Int) -> Int
                let visit (n) = if n > 5 then %s else 3

                example visit
                    | "far" : (6) -> 1
                    | "near" : (5) -> 3
                """;
        Compilation helper = compiled(visit.formatted("fee(Station { at = \"x\" })"));
        Compilation written = compiled(visit.formatted("1"));
        assertEquals(List.of(1), provenUnreachable(helper),
                "the Renkei arm and not the OnceKind arm, before any row is run");
        assertEquals(List.of("Station is never Renkei"), whyDead(helper));
        assertEquals(List.of(), open(helper), "nothing holds the verdict open");
        assertEquals(AdequacyReport.of(written).adequacy(), AdequacyReport.of(helper).adequacy());
        assertEquals(gaps(written), gaps(helper));
    }

    /**
     * The arms of the source's own forks proven unreachable, by their place in the fork — read
     * before the rows, which a row going through such an arm would otherwise take back.
     */
    private static List<Integer> provenUnreachable(Compilation compilation) {
        List<Integer> out = new ArrayList<>();
        compilation.db().ask(new Adequacy.PathReached("demo")).value().values()
                .forEach(answers -> answers.found().forEach((where, said) -> {
                    if (where instanceof ControlPlace.Arm arm && arm.writtenBy("demo")
                            && said instanceof souther.compiler.reach.Reachability.Unreachable) {
                        out.add(arm.part());
                    }
                }));
        return out;
    }

    private static List<Adequacy.Kind> gaps(Compilation compilation) {
        return AdequacyReport.of(compilation).adequacyGaps().stream()
                .map(Adequacy.Finding::kind).toList();
    }

    private static List<String> deadBranches(Compilation compilation) {
        return compilation.warnings().stream().map(each -> each.diagnostic().code())
                .filter("E1327"::equals).toList();
    }

    /** For each dead branch, what case the value matched on was said to be and was not. */
    private static List<String> whyDead(Compilation compilation) {
        return compilation.warnings().stream().map(each -> each.diagnostic())
                .filter(each -> each.code().equals("E1327"))
                .map(each -> each.notes().stream().map(Note::said)
                        .filter(DeadBranchMessage.TheValueMatchedOnIsNeverItsCase.class::isInstance)
                        .map(DeadBranchMessage.TheValueMatchedOnIsNeverItsCase.class::cast)
                        .map(said -> said.canBe() + " is never " + said.cases())
                        .findFirst().orElse("nothing more"))
                .toList();
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
