package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.coverage.ControlPlace;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * Whether what {@code List.filter} kept holds anything is whether some element met the closure it
 * was handed, and a fork on it turns on what the closure answered.
 *
 * <p>The size of what the filter kept is a number nothing in the input holds, so a fork read as
 * that size against nought is a rule about a value made from the input, and nothing reads it. Read
 * as what the closure answered, the fork is about the positions the closure reads — and over a list
 * written out, about the rules the closure states for each element written there.
 *
 * <p>The emptiness check and the size against nought are one statement, so each is held to the
 * other. A size held against any other number counts what was kept, which no answer of the closure
 * states, and is still a rule about a value made from the input.
 */
class AnEmptinessOfWhatAFilterKeptIsWhatItsClosureAnswersTest {

    private static final String TRIP = """
            data Trip = { cost: Int, abroad: Bool }
            data Reason = High | Abroad

            behavior submit : (t: Trip) -> Int
            """;

    private static final String APPLIES = """
            let applies (t: Trip, r: Reason): Bool =
                match r with
                    | High -> t.cost >= 100
                    | Abroad -> t.abroad
            """;

    private static final String REASONS_OF = """
            let reasonsOf (t: Trip): List<Reason> =
                List.filter(r -> applies(t, r), [High, Abroad])
            """;

    private static final String ROWS = """

            example submit
                | "cheap and home" : (Trip { cost = 99, abroad = false }) -> 1
                | "expensive" : (Trip { cost = 100, abroad = false }) -> 2
                | "abroad" : (Trip { cost = 99, abroad = true }) -> 2
                | "well above" : (Trip { cost = 1000, abroad = false }) -> 2
                | "free" : (Trip { cost = 0, abroad = false }) -> 1
            """;

    /** The reasons a trip needs approval for, built by a helper and asked whether there are any. */
    private static final String THE_REASONS_A_HELPER_BUILT = TRIP + APPLIES + REASONS_OF + """
            let submit (t) = {
                let reasons = reasonsOf(t)
                if List.isEmpty(reasons) then 1 else 2
            }
            """ + ROWS;

    /**
     * Every rule the closure states is read, each at the line it draws for the element written
     * there — the cost at a hundred for {@code High}, and whether the trip is abroad for
     * {@code Abroad} — and the rows meet the measure.
     */
    @Test
    void theReasonsAHelperBuiltAreReadAsWhatTheyWereKeptFor() {
        Compilation compilation = compiled(THE_REASONS_A_HELPER_BUILT);
        assertEquals(List.of(), measured(compilation).notRead(), "every rule is read");
        assertEquals(List.of("[t.cost/x < 100, t.cost/100 <= x]", "[true, false]"),
                measured(compilation).axes().stream()
                        .map(axis -> String.valueOf(axis.classes())).toList());
        assertEquals(AdequacyReport.AdequacyStatus.SATISFIED,
                AdequacyReport.of(compilation).adequacy());
    }

    /** And the size against nought is the same statement, with nothing read differently. */
    @Test
    void theSizeAgainstNoughtIsTheSameStatement() {
        assertTheSame(THE_REASONS_A_HELPER_BUILT, THE_REASONS_A_HELPER_BUILT.replace(
                "List.isEmpty(reasons)", "List.length(reasons) == 0"));
        assertTheSame(THE_REASONS_A_HELPER_BUILT.replace("List.isEmpty(reasons) then 1 else 2",
                        "Bool.not(List.isEmpty(reasons)) then 2 else 1"),
                THE_REASONS_A_HELPER_BUILT.replace("List.isEmpty(reasons) then 1 else 2",
                        "List.length(reasons) /= 0 then 2 else 1"));
    }

    /** However many helpers the author put between the fork and the closure. */
    @Test
    void theHelpersBetweenAreNoPartOfWhatItMeans() {
        String inline = TRIP + """
                let submit (t) =
                    if List.isEmpty(List.filter(r -> match r with
                            | High -> t.cost >= 100
                            | Abroad -> t.abroad, [High, Abroad])) then 1 else 2
                """ + ROWS;
        String filterInline = TRIP + APPLIES + """
                let submit (t) =
                    if List.isEmpty(List.filter(r -> applies(t, r), [High, Abroad])) then 1 else 2
                """ + ROWS;
        String closureInline = TRIP + """
                let reasonsOf (t: Trip): List<Reason> =
                    List.filter(r -> match r with
                            | High -> t.cost >= 100
                            | Abroad -> t.abroad, [High, Abroad])
                let submit (t) = if List.isEmpty(reasonsOf(t)) then 1 else 2
                """ + ROWS;
        assertTheSame(inline, THE_REASONS_A_HELPER_BUILT);
        assertTheSame(inline, filterInline);
        assertTheSame(inline, closureInline);
    }

    /** Over a position, the closure's rule is about each element the position holds. */
    @Test
    void overAPositionTheRuleIsAboutItsElements() {
        String lines = """
                data Line = { price: Int }
                data Order = { lines: List<Line> }

                behavior bill : (o: Order) -> Int
                let bill (o) = if %s then 1 else 2
                """;
        PartitionEvidence empty = measured(compiled(lines.formatted(
                "List.isEmpty(List.filter(l -> l.price > 0, o.lines))")));
        assertEquals(List.of(), empty.notRead(), "the element's price is read");
        assertEquals(toldApart(measured(compiled(lines.formatted(
                        "Bool.not(List.any(l -> l.price > 0, o.lines))")))),
                toldApart(empty), "as the quantifier the check denies is");
    }

    /** How many were kept is no answer the closure gives, and is not read as one. */
    @Test
    void howManyWereKeptIsAValueMadeFromTheInput() {
        PartitionEvidence counted = measured(compiled(TRIP + APPLIES + """
                let submit (t) =
                    if List.length(List.filter(r -> applies(t, r), [High, Abroad])) >= 2
                    then 2 else 1
                """));
        assertEquals(List.of("t.cost RULE_ABOUT_A_DERIVED_VALUE",
                        "t.abroad RULE_ABOUT_A_DERIVED_VALUE"),
                counted.notRead().stream().map(each -> each.at() + " " + each.reason()).toList());
    }

    /**
     * A closure that answers the same for every element leaves whether anything was kept to the
     * container, in either spelling.
     *
     * <p>Refusing every element keeps nothing, whatever the order holds, so the fork turns on
     * nothing. Keeping every element keeps what the order holds, and the fork turns on whether the
     * filter's container holds anything — a value made from the lines, the same whichever way the
     * check is written.
     */
    @Test
    void aClosureThatAnswersTheSameLeavesItToTheContainer() {
        String lines = """
                data Line = { price: Int }
                data Order = { lines: List<Line>, coupon: Int }

                behavior bill : (o: Order) -> Int
                let bill (o) = if %s && o.coupon > 5 then 1 else 2
                """;
        for (String kept : List.of("l -> true", "l -> false")) {
            String filter = "List.filter(" + kept + ", o.lines)";
            assertEquals(
                    notRead(measured(compiled(lines.formatted("List.length(" + filter + ") == 0")))),
                    notRead(measured(compiled(lines.formatted("List.isEmpty(" + filter + ")")))),
                    kept);
        }
        assertEquals(List.of(), notRead(measured(compiled(lines.formatted(
                "List.isEmpty(List.filter(l -> false, o.lines))")))), "nothing is ever kept");
        assertEquals(List.of("o.lines RULE_ABOUT_A_DERIVED_VALUE"), notRead(measured(compiled(
                lines.formatted("List.isEmpty(List.filter(l -> true, o.lines))")))),
                "what is kept is what the lines hold");
    }

    /**
     * A check of a container the input's rules leave holding something comes to the same in either
     * spelling: the same arm nothing reaches, the same dead branch said about it, and the same
     * measures over what is left.
     *
     * <p>Only what a reader of the measure sees. How a reading on the way settles the check is its
     * own, and two spellings agreeing there is not the claim — what they come to is.
     */
    @Test
    void aContainerTheRulesLeaveHoldingSomethingIsCheckedTheSameInEitherSpelling() {
        String box = """
                data Box = { xs: List<Int> }
                    invariant List.length(xs) >= 1

                behavior f : (x: Box) -> Int
                let f (x) = if %s then 2 else 1

                example f
                    | "one" : (Box { xs = [1] }) -> 1
                """;
        Seen call = seen(box.formatted("List.isEmpty(x.xs)"));
        Seen size = seen(box.formatted("List.length(x.xs) == 0"));
        assertEquals(List.of(0), call.unreachableArms(), "nothing reaches the arm the check holds on");
        assertEquals(List.of("E1327"), call.deadBranches(), "and that is said");
        assertEquals(call, size);
    }

    /**
     * What a reader of the measures is shown of {@code f}.
     *
     * @param unreachableArms which arms of the body's own forks were proven nothing reaches
     * @param deadBranches    the dead branches the build reports
     * @param branch          the arms counted and the arms a row goes through
     * @param decisionRules   how many rules what the body decides holds
     * @param adequacy        the verdict
     */
    private record Seen(List<Integer> unreachableArms, List<String> deadBranches,
                        List<Integer> branch, int decisionRules,
                        AdequacyReport.AdequacyStatus adequacy) {}

    private static Seen seen(String model) {
        Compilation compilation = compiled(model);
        List<Integer> unreachable = new ArrayList<>();
        compilation.db().ask(new Adequacy.Arrived("demo")).value().get("f").answers().found()
                .forEach((where, said) -> {
                    if (where instanceof ControlPlace.Arm arm && arm.writtenBy("demo")
                            && said instanceof souther.compiler.reach.Reachability.Unreachable) {
                        unreachable.add(arm.part());
                    }
                });
        Adequacy.BranchEvidence branch =
                compilation.db().ask(new Adequacy.BranchCoverage("demo")).value().get("f");
        return new Seen(unreachable,
                compilation.warnings().stream().map(each -> each.diagnostic().code())
                        .filter("E1327"::equals).toList(),
                List.of(branch.arms().counted(), branch.arms().covered()),
                compilation.db().ask(new Adequacy.DecisionReadings("demo")).value().get("f")
                        .rules().size(),
                AdequacyReport.of(compilation).adequacy());
    }

    /** Both spellings read every rule alike, tell the same apart and come to one verdict. */
    private static void assertTheSame(String one, String other) {
        Compilation first = compiled(one);
        Compilation second = compiled(other);
        assertEquals(List.of(), measured(first).notRead());
        assertEquals(notRead(measured(first)), notRead(measured(second)));
        assertEquals(toldApart(measured(first)), toldApart(measured(second)));
        assertEquals(AdequacyReport.of(first).adequacy(), AdequacyReport.of(second).adequacy());
    }

    private static List<String> notRead(PartitionEvidence evidence) {
        return evidence.notRead().stream().map(each -> each.at() + " " + each.reason()).toList();
    }

    private static List<String> toldApart(PartitionEvidence evidence) {
        return evidence.axes().stream()
                .map(axis -> axis.classes() + " " + axis.toldApart()).toList();
    }

    private static PartitionEvidence measured(Compilation compilation) {
        Map<String, PartitionEvidence> coverage =
                compilation.db().ask(new Adequacy.Coverage("demo")).value();
        assertNotNull(coverage, () -> "the model under test compiles: " + compilation.errors());
        assertEquals(1, coverage.size(), "one behavior");
        return coverage.values().iterator().next();
    }

    private static Compilation compiled(String model) {
        Compilation compilation = Compilation.ofSource("module demo\n\n" + model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors(), "the model compiles and its rows hold");
        return compilation;
    }
}
