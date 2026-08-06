package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.Diagnostic;
import souther.compiler.observe.Disposition;
import souther.compiler.observe.MeasurementStatus;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.Db;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.time.Duration;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What is said when some of what a row wrote could not be read.
 *
 * <p>The whole feature rests on three answers where two would fit: met, unmet, and *not decided*. The
 * measures each knew that, and the aggregate in front of them did not — it handed on the rows and
 * dropped the reasons the rest were missing, so every measure downstream read "what was observed" as
 * "what there was". These hold each of them to the third answer.
 */
class CompilePartialAdequacyTest {

    /** A row that never comes back: the helper loops, so its evaluation is stopped rather than
     * finished, and what it went through on the way goes with it. */
    private static final String TIMES_OUT = """
            module example.loop

            data Draft = { n: Int }
            data Done = { n: Int }
            data Small = { n: Int }

            partial let spin (n: Int): Int = spin(n)

            behavior go : (request: Draft) -> Done | Small
                constructs Done, Small

            let go (request) = {
                guard request.n <= 0 else Done { n = spin(request.n) }
                Small { n = request.n }
            }

            example go
                | (Draft { n = 1 }) -> Done { n = 1 }
            """;

    /**
     * An input whose observation is cut short before the position a rule is about.
     *
     * <p>The collection ahead of it spends the node budget, so `cost` is truncated — while the row
     * writes exactly the number the invariant's lower bound names.
     */
    private static String budgetSpent(String tail) {
        StringBuilder inner = new StringBuilder();
        for (int i = 0; i < 64; i++) {
            inner.append(i == 0 ? "" : ", ")
                    .append("Item { a = \"").append(i).append("\", b = \"").append(i)
                    .append("\", c = \"").append(i).append("\" }");
        }
        StringBuilder groups = new StringBuilder();
        for (int i = 0; i < 64; i++) {
            groups.append(i == 0 ? "" : ", ").append("Group { items = [ ").append(inner).append(" ] }");
        }
        return """
                module example.budget

                data Amount = Int
                    invariant value >= 0 && value <= 1000

                data Yes
                data No
                data Flag = Yes | No

                data Item = { a: String, b: String, c: String }
                data Group = { items: List<Item> }

                data Draft = { groups: List<Group>, cost: Amount, flag: Flag }
                data Ok = { n: Int }

                behavior take : (request: Draft) -> Ok
                    constructs Ok

                let take (request) = Ok { n = request.cost.value }

                example take
                    | (Draft { groups = [ %s ], cost = Amount(0), flag = Yes }) -> Ok { n = 0 }
                """.formatted(groups) + tail;
    }

    /** Compiles are shared between the cases that read the same model, keyed by the budget as well as
     * the source: the two are what a compile here is, and a model read under one of them says nothing
     * about what it would say under the other. */
    private static final Map<String, Compilation> COMPILED = new java.util.LinkedHashMap<>();

    /** A model that comes back, on the default budget — including {@link #budgetSpent}, which walks
     * four thousand nodes and is the reason a short budget cannot be set for the whole suite. */
    private static Compilation measured(String source) {
        return measured(source, (Deadline) null);
    }

    /** As {@link #measured(String)}, for a model whose rows do not come back: waiting out the default
     * budget reaches the same answer, later. */
    private static Compilation measured(String source, Duration budget) {
        return compiled("report:", source, budget, Adequacy.Asked.reportOnly());
    }

    private static Compilation warned(String source) {
        return warned(source, null);
    }

    private static Compilation warned(String source, Duration budget) {
        return compiled("warn:", source, budget, Adequacy.Asked.warningsAt(Adequacy.Level.ALL));
    }

    private static Compilation compiled(String what, String source, Duration budget,
                                        Adequacy.Asked asked) {
        return COMPILED.computeIfAbsent(what + budget + ":" + source, _ -> {
            Compilation compilation = Compilation.ofSource(source, "Main");
            if (budget != null) {
                compilation.withExampleBudget(budget);
            }
            compilation.measure(asked);
            compilation.answerEverything();
            return compilation;
        });
    }

    /** Measured, with {@code overrun} the work this model does not get back from — for a model
     *  written out here, which is its own key. */
    private static Compilation measured(String source, Deadline overrun) {
        return measured("report:", source, overrun, Adequacy.Asked.reportOnly());
    }

    /** The same, for a model shared between tests, which needs a key of its own. */
    private static Compilation measured(String key, String source, Deadline overrun) {
        return measured("report:" + key, source, overrun, Adequacy.Asked.reportOnly());
    }

    /** The same, warned about at every level. */
    private static Compilation warned(String key, String source, Deadline overrun) {
        return measured("warn:" + key, source, overrun,
                Adequacy.Asked.warningsAt(Adequacy.Level.ALL));
    }

    /**
     * Measured, with {@code overrun} the work this model does not get back from.
     *
     * <p>Said rather than timed. What these tests are about is what a measure makes of a row that did
     * not come back, and a model that loops plus a clock short enough to catch it also reports the
     * rows that were supposed to finish as rows that did not, on any host loaded enough to make it
     * so.
     */
    private static Compilation measured(String key, String source, Deadline overrun,
                                        Adequacy.Asked asked) {
        return COMPILED.computeIfAbsent(key + ":" + source, _ -> {
            Compilation compilation = Compilation.ofSource(source, "Main");
            compilation.withDeadline(overrun);
            compilation.measure(asked);
            compilation.answerEverything();
            return compilation;
        });
    }

    private static List<String> warningCodes(Compilation compilation) {
        List<String> codes = new ArrayList<>();
        for (Db.Found found : compilation.db().allReports()) {
            Diagnostic d = found.report().diagnostic();
            if (!found.report().isError() && d.code() != null && d.code().startsWith("E19")) {
                codes.add(d.code());
            }
        }
        return codes;
    }

    /**
     * A row that did not finish went somewhere before it stopped.
     *
     * <p>What it went through was dropped with it, so the arms it did not light are undecided rather
     * than unreached — and every arm of the behavior would otherwise be reported as one no row goes
     * through, on the strength of a run nobody let finish.
     */
    @Test
    void aBranchMeasureOverAnUnfinishedRowIsUndecided() {
        Compilation compilation = measured("loop", TIMES_OUT, DoesNotComeBack.overrunningOn(DoesNotComeBack.everythingAboutRowsOf("go")));
        Adequacy.BranchEvidence branch = compilation.db()
                .ask(new Adequacy.BranchCoverage(compilation.modules().get(0))).value().get("go");

        assertEquals(2, branch.all().size(), "the arms are there");
        assertEquals(MeasurementStatus.PARTIAL, branch.status());
        assertEquals(List.of(), branch.covered().stream().sorted().toList());
    }

    /** And nothing is warned about from it. */
    @Test
    void anUndecidedBranchMeasureWarnsAboutNoArm() {
        assertFalse(warningCodes(warned("loop", TIMES_OUT, DoesNotComeBack.overrunningOn(DoesNotComeBack.everythingAboutRowsOf("go")))).contains("E1918"),
                "an arm a row might have gone through is not an arm nothing reaches");
    }

    /**
     * A value the observation could not reach is not a value that missed.
     *
     * <p>The row here writes the very number the invariant's lower bound names. Its observation was
     * cut short by a limit reached elsewhere in the same input, and reporting that as "no row is at
     * this boundary" states something about the model that is not true.
     */
    @Test
    void aBoundaryWhosePositionWasNotReadIsUndecided() {
        PartitionEvidence partition = measured(budgetSpent("")).db()
                .ask(new Adequacy.Coverage("example.budget")).value().get("take");

        List<PartitionEvidence.BoundaryCoverage> at = partition.boundaries().stream()
                .filter(b -> b.value().equals("0")).toList();
        assertEquals(1, at.size());
        assertEquals(MeasurementStatus.PARTIAL, at.get(0).status());
        assertFalse(at.get(0).hit(), "nothing was read, so nothing was met either");
    }

    @Test
    void anUndecidedBoundaryWarnsAboutNothing() {
        assertFalse(warningCodes(warned(budgetSpent(""))).contains("E1916"),
                "a boundary whose position was not read is not a boundary nothing is at");
    }

    /**
     * A class a row may already sit in is not a class to write a row for.
     *
     * <p>The worst of these to get wrong. A warning is a claim; a generated row is a specific piece of
     * work handed to a person, and handing them work that is already done is worse than saying nothing.
     */
    @Test
    void nothingIsGeneratedForAPositionThatCouldNotBeRead() {
        Compilation compilation = measured(budgetSpent(""));
        Map<String, Adequacy.Filling> generated = compilation.db()
                .ask(new Adequacy.Generated("example.budget")).value();
        assertNotNull(generated);

        assertEquals(List.of(), generated.get("take").pairs().rows(),
                "the flag's classes are undecided, so nothing is written for them");
        assertFalse(generated.get("take").pairs().incompleteness().isEmpty(),
                "and the position that could not be read is named");
        assertEquals("", GeneratedRows.of("example.budget", generated, true));
    }

    /**
     * The rows the compile ran are what every measure reads, reasons included.
     *
     * <p>The evaluation keeps observations and the reasons for their absence apart on purpose. An
     * aggregate that passed on the first and dropped the second would answer as if the reason were
     * nothing, which is the one reading the whole design is against.
     */
    @Test
    void whatStoppedARowBeingSeenReachesTheMeasureThatReadsIt() {
        Compilation compilation = measured("loop", TIMES_OUT, DoesNotComeBack.overrunningOn(DoesNotComeBack.everythingAboutRowsOf("go")));
        Adequacy.SignatureEvidence signature = compilation.db()
                .ask(new Adequacy.Witnesses(compilation.modules().get(0))).value().get("go");

        assertEquals(MeasurementStatus.PARTIAL, signature.status());
        assertFalse(warningCodes(warned("loop", TIMES_OUT, DoesNotComeBack.overrunningOn(DoesNotComeBack.everythingAboutRowsOf("go")))).contains("E1913"),
                "a case the unfinished row might have produced is not a case nothing claims");
    }

    /**
     * A report about one behavior says nothing about another.
     *
     * <p>`--behavior submit` is a promise about what the output is about. A status of `partial` whose
     * reason names a behavior the report does not show is a status nothing in front of the reader
     * accounts for.
     */
    @Test
    void filteringToOneBehaviorLeavesAnotherBehaviorsReasonsBehind() {
        Compilation compilation = measured("""
                module example.two

                data Draft = { n: Int }
                data Ok = { n: Int }
                data Gone = { why: String }

                partial let spin (n: Int): Int = spin(n)

                behavior submit : (request: Draft) -> Ok
                    constructs Ok

                let submit (request) = Ok { n = request.n }

                behavior cancel : (request: Draft) -> Gone
                    constructs Gone

                let cancel (request) = Gone { why = "x" }

                example submit
                    | (Draft { n = 1 }) -> Ok { n = 1 }

                example cancel
                    | (Draft { n = spin(1) }) -> Gone { why = "x" }
                """, DoesNotComeBack.overrunningOn(DoesNotComeBack.everythingAboutRowsOf("cancel")));
        AdequacyReport whole = AdequacyReport.of(compilation);

        assertEquals(MeasurementStatus.PARTIAL, whole.status(), "`cancel` did not finish");
        assertEquals(List.of("cancel"), whole.modules().get(0).incompleteness().stream()
                .map(souther.compiler.observe.Incompleteness::subject).toList());

        AdequacyReport one = whole.only(null, "submit");
        assertEquals(MeasurementStatus.COMPLETE, one.status());
        assertEquals(List.of(), one.modules().get(0).incompleteness());
        assertTrue(one.modules().get(0).behaviors().stream()
                .allMatch(b -> b.name().equals("submit")));
    }

    // --- a source whose rows nothing read at all ------------------------------------------------

    /**
     * One source read, one not.
     *
     * <p>The attached file declares a name the module already declares, so its rows would read that
     * other declaration and it is not evaluated (E1906). It leaves no rows and one reason — and the
     * rows it holds are at both boundaries and in the class the module's own row is not.
     */
    private static final List<String> SPLIT = List.of("""
            module example.split

            data Amount = Int
                invariant value >= 0 && value <= 1000

            data Yes
            data No
            data Flag = Yes | No

            data Draft = { cost: Amount, flag: Flag }
            data Ok = { n: Int }
            data Refused = { why: String }

            let shared = Draft { cost = Amount(7), flag = Yes }

            behavior take : (request: Draft) -> Ok | Refused
                constructs Ok

            let take (request) = Ok { n = request.cost.value }

            example take
                | (Draft { cost = Amount(7), flag = Yes }) -> Ok { n = 7 }
            """, """
            examples for example.split

            let shared = Draft { cost = Amount(0), flag = No }

            example take
                | (Draft { cost = Amount(0), flag = No }) -> Ok { n = 0 }
                | (Draft { cost = Amount(1000), flag = No }) -> Ok { n = 1000 }
            """);

    private static Compilation split() {
        return COMPILED.computeIfAbsent("split", _ -> {
            Compilation compilation = Compilation.ofSources(SPLIT,
                    souther.compiler.meta.ModulePath.EMPTY);
            compilation.measure(Adequacy.Asked.reportOnly());
            compilation.answerEverything();
            return compilation;
        });
    }

    /**
     * A boundary the unread rows are at is not a boundary nothing is at.
     *
     * <p>The axes already knew this; the boundaries were reading only the rows that remained. Being
     * found still settles it — one row at the value is one row at the value, whatever went unread —
     * but not being found among some of the rows settles nothing.
     */
    @Test
    void aBoundaryIsUndecidedWhereSomeRowsWereNeverRead() {
        PartitionEvidence partition = split().db()
                .ask(new Adequacy.Coverage("example.split")).value().get("take");

        assertEquals(2, partition.boundaries().size());
        for (PartitionEvidence.BoundaryCoverage boundary : partition.boundaries()) {
            assertEquals(MeasurementStatus.PARTIAL, boundary.status(), boundary.value());
            assertFalse(boundary.hit());
        }
    }

    /**
     * And nothing is generated from it.
     *
     * <p>Both rows the generator would write are sitting in the file it could not read. A row that
     * could not be classified stops its own position; a row that was never seen stops the behavior,
     * because which positions it would have settled is exactly what is unknown.
     */
    @Test
    void nothingIsGeneratedWhereSomeRowsWereNeverRead() {
        Map<String, Adequacy.Filling> generated = split().db()
                .ask(new Adequacy.Generated("example.split")).value();

        assertEquals(List.of(), generated.get("take").pairs().rows());
        assertEquals(List.of(), generated.get("take").boundaries().rows());
        assertEquals("", GeneratedRows.of("example.split", generated, true));
    }

    /**
     * A reason that names no behavior belongs to every behavior.
     *
     * <p>Filtering to one behavior drops the reasons about the others. A whole source that could not
     * be evaluated is not about another behavior — it is missing rows for whatever it held, this one
     * included — so it stays, and the status with it.
     */
    @Test
    void filteringKeepsAReasonThatIsAboutNoOneBehavior() {
        AdequacyReport one = AdequacyReport.of(split()).only(null, "take");

        assertEquals(MeasurementStatus.PARTIAL, one.status());
        assertEquals(1, one.modules().get(0).incompleteness().size());
        assertEquals(souther.compiler.observe.Incompleteness.Code.RUNTIME_ABSENT,
                one.modules().get(0).incompleteness().get(0).code());
    }

    /**
     * The lines say what the summary says.
     *
     * <p>A `(partial)` in the margin and a flat assertion under it read as a finding with a footnote.
     * Under partial the honest sentence is that nothing *seen* claims the case.
     */
    @Test
    void aSignatureLineUnderPartialDoesNotAssert() {
        String human = AdequacyReport.of(split()).human();

        assertTrue(human.contains("undecided whether a row expects `Refused`"), human);
        assertFalse(human.contains("· no row expects"), human);
    }

    // --- what the status above a measure says -----------------------------------------------------

    /**
     * A measure that could not be made shows in the status over it.
     *
     * <p>Here nothing is recorded as a reason at all: the truncation is inside the value a row wrote,
     * and the measure that reads it is where it becomes visible. A report opening with `complete` over
     * a line reading `undecided` is the confusion this field exists to prevent.
     */
    @Test
    void aPartialMeasureMakesTheStatusAboveItPartial() {
        AdequacyReport report = AdequacyReport.of(measured(budgetSpent("")));

        assertEquals(MeasurementStatus.PARTIAL, report.status());
        assertEquals(MeasurementStatus.PARTIAL, report.modules().get(0).status());
        assertEquals(MeasurementStatus.PARTIAL, report.modules().get(0).behaviors().get(0).status());
        assertEquals(List.of(), report.modules().get(0).incompleteness(),
                "and it is not because something was reported as a reason");
    }

    /**
     * What the human report suppresses, the JSON suppresses.
     *
     * <p>A field named `unreached` holding an arm nothing watched says something that is not so, and
     * reading `status` beside it does not undo the name.
     */
    @Test
    void theJsonNamesNoUnreachedArmUnderPartial() throws Exception {
        JsonNode branch = JsonMapper.builder().build().readTree(
                AdequacyReport.of(measured("loop", TIMES_OUT, DoesNotComeBack.overrunningOn(DoesNotComeBack.everythingAboutRowsOf("go")))).json())
                .get("modules").get(0).get("behaviors").get(0).get("branch");

        assertEquals("partial", branch.get("status").asString());
        assertEquals(2, branch.get("arms").asInt());
        assertEquals(0, branch.get("unreached").size());
    }

    /**
     * A combination an unread row may sit in has not been left untried by anybody.
     *
     * <p>The other measures each say whether their numbers are over all the rows or some of them; the
     * pair space was the one that could not, so its count of untried combinations read as a finding.
     */
    @Test
    void thePairSpaceSaysWhetherItSawEveryRow() {
        Compilation compilation = measured("""
                module example.pair

                data Yes
                data No
                data Flag = Yes | No

                data Ok = { n: Int }

                partial let spin (n: Int): Int = spin(n)

                behavior pick : (a: Flag, b: Flag) -> Ok
                    constructs Ok

                let pick (a, b) = Ok { n = spin(1) }

                example pick
                    | (Yes, Yes) -> Ok { n = 0 }
                """, DoesNotComeBack.overrunningOn(DoesNotComeBack.everyRowOf("pick")));
        PartitionEvidence partition = compilation.db()
                .ask(new Adequacy.Coverage("example.pair")).value().get("pick");

        assertEquals(4, partition.pairs().total());
        assertEquals(MeasurementStatus.PARTIAL, partition.pairs().status(),
                "the one row could not be placed at either position");
        assertFalse(AdequacyReport.of(compilation).human().contains("untried"),
                AdequacyReport.of(compilation).human());
    }

    /**
     * The positions and the combinations over them answer from one reading.
     *
     * <p>They were putting the same question to the rows and answering the follow-up differently: the
     * positions counted the row nothing could place and called their classes undecided, the
     * combinations left it out and called theirs untried. Two sentences from one row, printed one
     * after the other.
     */
    @Test
    void thePositionsAndTheCombinationsAgree() {
        Compilation compilation = measured("""
                module example.agree

                data Yes
                data No
                data Flag = Yes | No

                data Ok = { n: Int }

                partial let spin (n: Int): Int = spin(n)

                behavior pick : (a: Flag, b: Flag) -> Ok
                    constructs Ok

                let pick (a, b) = Ok { n = spin(1) }

                example pick
                    | (Yes, Yes) -> Ok { n = 0 }
                """, DoesNotComeBack.overrunningOn(DoesNotComeBack.everyRowOf("pick")));
        PartitionEvidence partition = compilation.db()
                .ask(new Adequacy.Coverage("example.agree")).value().get("pick");

        for (PartitionEvidence.AxisCoverage axis : partition.axes()) {
            assertEquals(MeasurementStatus.PARTIAL, axis.status(), axis.path());
        }
        assertEquals(MeasurementStatus.PARTIAL, partition.pairs().status());
    }

    /**
     * A hit is a hit whatever else stopped.
     *
     * <p>Found is decidable over some of the rows; not-found is not. A row that wrote the boundary
     * value and went through the comparison did so, and hiding that because another row never
     * finished throws away the one thing that was settled.
     */
    @Test
    void aBoundaryARowDemonstrablyMetStaysMet() {
        PartitionEvidence partition = measured("mix", """
                module example.mix

                data Amount = Int
                    invariant value >= 0

                data Domestic
                data Overseas
                data Kind = Domestic | Overseas

                data Draft = { kind: Kind, cost: Amount }
                data Ok = { n: Int }
                data Big = { n: Int }

                partial let spin (n: Int): Int = spin(n)

                behavior take : (request: Draft) -> Ok | Big
                    constructs Ok, Big

                let take (request) = {
                    guard request.cost.value <= 100 else Big { n = spin(request.cost.value) }
                    Ok { n = request.cost.value }
                }

                example take
                    | "at the line" : (Draft { kind = Overseas, cost = Amount(100) }) -> Ok { n = 100 }
                    | "over it"     : (Draft { kind = Domestic, cost = Amount(500) }) -> Big { n = 0 }
                """, DoesNotComeBack.overrunningOn(
                        DoesNotComeBack.everythingAboutTheRowDescribed("over it")), Adequacy.Asked.reportOnly())
                .db().ask(new Adequacy.Coverage("example.mix")).value().get("take");

        PartitionEvidence.BoundaryCoverage line = partition.boundaries().stream()
                .filter(b -> b.value().equals("100")).findFirst().orElseThrow();
        assertTrue(line.hit(), "a row wrote 100 and went through the comparison");
        assertEquals(MeasurementStatus.COMPLETE, line.status());

        PartitionEvidence.BoundaryCoverage beyond = partition.boundaries().stream()
                .filter(b -> b.value().equals("101")).findFirst().orElseThrow();
        assertEquals(MeasurementStatus.PARTIAL, beyond.status(),
                "and the one nothing was found at is undecided, not missed");
    }

    /**
     * One row of two written under separate {@code example} blocks does not come back, and the other
     * is evaluated as it would have been.
     *
     * <p>Here because a behavior can be exampled more than once — a second block beside the first, or
     * an {@code examples for} file beside the model — and the first thing this was written with named
     * a row by its number within its block. That made both first rows one name, so picking out either
     * picked out both, and a model of this shape would have had its working rows reported as rows that
     * did not come back.
     */
    @Test
    void aRowIsPickedOutOfTheBlockItIsInAndNoOther() {
        Compilation compilation = measured("""
                module example.twice

                data Draft = { n: Int }
                data Ok = { n: Int }

                behavior take : (request: Draft) -> Ok
                    constructs Ok

                let take (request) = Ok { n = request.n }

                example take
                    | "does not come back" : (Draft { n = 1 }) -> Ok { n = 1 }

                example take
                    | "comes back" : (Draft { n = 2 }) -> Ok { n = 2 }
                """,
                DoesNotComeBack.overrunningOn(
                        DoesNotComeBack.everythingAboutTheRowDescribed("does not come back")));

        List<String> codes = new ArrayList<>();
        for (Db.Found found : compilation.db().allReports()) {
            codes.add(String.valueOf(found.report().diagnostic().code()));
        }
        assertEquals(1, codes.stream().filter("E1923"::equals).count(),
                "one row was picked out, so one row did not come back: " + codes);
    }

    // --- who a reason counts against ---------------------------------------------------------------

    /**
     * A reason larger than a behavior counts against every behavior it holds.
     *
     * <p>`subject` carried a behavior name, a source id, the module or a position in one string, and
     * three readers worked out which from the shape of it — differently. The aggregate treated a
     * module-wide reason as a behavior nobody declared, the report matched it by name and found none,
     * and each was a defect found on its own. The scope is on the reason now, so nobody guesses.
     */
    @Test
    void aReasonAboutASourceCountsAgainstTheBehaviorsInIt() {
        souther.compiler.observe.Incompleteness aboutOne =
                souther.compiler.observe.Incompleteness.of(
                        souther.compiler.observe.Incompleteness.Code.ROW_UNDECIDED,
                        souther.compiler.observe.Incompleteness.Scope.BEHAVIOR, "submit");
        souther.compiler.observe.Incompleteness aboutTheSource =
                souther.compiler.observe.Incompleteness.of(
                        souther.compiler.observe.Incompleteness.Code.RUNTIME_ABSENT,
                        souther.compiler.observe.Incompleteness.Scope.SOURCE, "3");

        assertTrue(aboutOne.countsAgainst("submit"));
        assertFalse(aboutOne.countsAgainst("cancel"));
        assertTrue(aboutTheSource.countsAgainst("submit"));
        assertTrue(aboutTheSource.countsAgainst("cancel"),
                "nothing in the source was read, whichever behaviors it wrote rows for");
    }

    /** And the report says so: a behavior held by an unread source is not complete. */
    @Test
    void aBehaviorHeldByAnUnreadSourceIsNotComplete() {
        AdequacyReport report = AdequacyReport.of(split());

        assertEquals(MeasurementStatus.PARTIAL, report.status());
        for (AdequacyReport.BehaviorReport behavior : report.modules().get(0).behaviors()) {
            assertEquals(MeasurementStatus.PARTIAL, behavior.status(), behavior.name());
        }
    }

    /**
     * One reason is one entry, however many sources went looking.
     *
     * <p>These are structured rather than written out so that a build can count them, and a count that
     * grows with the number of attached files is counting the looking rather than the failure.
     */
    @Test
    void oneReasonIsReportedOnce() {
        List<souther.compiler.observe.Incompleteness> gaps =
                AdequacyReport.of(split()).modules().get(0).incompleteness();

        assertEquals(gaps.stream().map(souther.compiler.observe.Incompleteness::identity)
                        .distinct().count(), gaps.size(), gaps.toString());
    }

    /** The row that did not finish is still there to be counted, and still says it did not. */
    @Test
    void theUnfinishedRowIsStillReported() {
        Compilation compilation = measured("loop", TIMES_OUT, DoesNotComeBack.overrunningOn(DoesNotComeBack.everythingAboutRowsOf("go")));
        String sourceId = compilation.exampleSourcesOf("example.loop").get(0);

        List<souther.compiler.observe.RowOutcome> rows = compilation.db()
                .ask(souther.compiler.query.Output.Examples.asked(
                        compilation.db(), "example.loop", sourceId)).value().rows();

        assertEquals(1, rows.size());
        assertEquals(Disposition.INCOMPLETE, rows.get(0).disposition());
    }
}
