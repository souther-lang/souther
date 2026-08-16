package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.SourceNameResolver;
import souther.compiler.observe.InputCaseEvidence;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.Db;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.report.GeneratedRows;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A model that says where it has no answer, measured against what it can be asked.
 *
 * <p>Reaching an {@code unreachable} is E1911, so a case behind one is a case no row may be written
 * at. Counted in, it is a gap that stays open however the model is exercised — and the model that
 * invents a fallback answer instead reports full coverage, so the report pays for the wrong one.
 *
 * <p>Three measures asked for that row, each deriving what there was to cover on its own. They are
 * measured together here for that reason: what the signature counts, what a position is divided into
 * and what the generator offers are one universe, and a test that fixed one of them would leave the
 * other two free to disagree with it again.
 */
class ACaseTheModelRulesOutIsNotOwedARowTest {

    /**
     * A case the model's own rules refuse, beside one it admits.
     *
     * <p>{@code Active} is never {@code Off}, so a row at {@code Off} is one the constructor
     * refuses (E1903) whatever the body says, and the {@code unreachable} says the same thing the
     * invariant does. {@code Pending} is a case with an answer and no row: a gap that is real,
     * beside one that is not. Without it, a measure that simply reported nothing would pass every
     * assertion here.
     */
    private static final String RULED_OUT = """
            module example.probe

            data On
            data Off
            data Pending
            data Flag = On | Off | Pending
            data Active = Flag invariant value /= Off
            data Answer = Int

            behavior pick : (f: Active) -> Answer
                constructs Answer

            let pick (f) = match f.value with
                | On      -> Answer(1)
                | Pending -> Answer(0)
                | Off     -> unreachable "an Active is never Off"

            example pick
                | "on" : (Active(On)) -> Answer(1)
            """;

    /**
     * A claim nothing settles.
     *
     * <p>{@code f /= g} refuses pairs and no value of {@code f} on its own, and it is a rule this
     * compiler does not take into what a position may hold — so nothing here says whether an
     * {@code Off} arrives, and the case keeps what it was owed.
     */
    private static final String UNPROVEN = """
            module example.probe

            data On
            data Off
            data Pending
            data Flag = On | Off | Pending
            data T = { f: Flag, g: Flag } invariant f /= g
            data Answer = Int

            behavior pick : (t: T) -> Answer
                constructs Answer

            let pick (t) = match t.f with
                | On      -> Answer(1)
                | Pending -> Answer(0)
                | Off     -> unreachable "the probe never passes Off"

            example pick
                | "on" : (T { f = On, g = Off }) -> Answer(1)
            """;

    private static Compilation measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        return compilation;
    }

    private static InputCaseEvidence input(String source, int at) {
        Compilation compilation = measured(source);
        Adequacy.SignatureEvidence signature = compilation.db()
                .ask(new Adequacy.Witnesses(compilation.modules().get(0))).value().get("pick");
        assertNotNull(signature, "the model under test compiles");
        return signature.inputs().get(at);
    }

    private static PartitionEvidence.AxisCoverage axis(String source) {
        return axis(source, "f");
    }

    private static PartitionEvidence.AxisCoverage axis(String source, String path) {
        Compilation compilation = measured(source);
        PartitionEvidence partition = compilation.db()
                .ask(new Adequacy.Coverage(compilation.modules().get(0))).value().get("pick");
        assertNotNull(partition, "the model under test compiles");
        return partition.axes().stream().filter(each -> each.path().equals(path))
                .findFirst().orElseThrow();
    }

    /**
     * The identity the three measures share.
     *
     * <p>A case stays declared — the type has it, and that is part of what the model says — and leaves
     * what the rows are held to. Asserting the arithmetic rather than the two numbers separately, so
     * that a case going missing from both sides at once cannot pass.
     */
    @Test
    void whatIsDeclaredIsWhatIsCoverableAndWhatIsRuledOut() {
        InputCaseEvidence input = input(RULED_OUT, 0);

        assertEquals(3, input.declared().size());
        assertEquals(1, input.excluded().size());
        assertEquals(input.declared().size(),
                input.coverable().size() + input.excluded().size());
        assertEquals(List.of("Off"), input.excluded().stream().map(each -> each.name()).toList());
    }

    /**
     * What takes a case out is the rules, and not the body saying so.
     *
     * <p>The same model with the {@code unreachable} replaced by an answer. Nothing declares
     * anything about {@code Off} and it is out of the denominator all the same, because
     * {@code Active}'s invariant is what refuses it — measured the other way round, an author was
     * asked for a row the constructor refuses whenever they had not written the claim.
     */
    @Test
    void whatTakesACaseOutIsTheRulesAndNotAClaim() {
        String answered = RULED_OUT.replace(
                "| Off     -> unreachable \"an Active is never Off\"", "| Off     -> Answer(9)");

        InputCaseEvidence input = input(answered, 0);

        assertEquals(List.of("Off"), input.excluded().stream().map(each -> each.name()).toList());
        assertEquals(List.of("Pending"),
                input.unspecified().stream().map(each -> each.name()).toList());
    }

    /**
     * A claim the rules contradict moves nothing.
     *
     * <p>{@code Flag} has {@code B} and nothing anywhere says a caller cannot pass one, so the row
     * is still owed. The body says otherwise, and what the body says is not what the denominator is
     * made of: taken at its word, the measure drops the one obligation whose discharge would have
     * shown the model wrong.
     */
    @Test
    void aClaimTheRulesContradictLeavesTheCaseOwed() {
        String claimed = """
                module example.probe

                data A
                data B
                data Kind = A | B
                data Answer = Int

                behavior pick : (k: Kind) -> Answer
                    constructs Answer

                let pick (k) = match k with
                    | A -> Answer(1)
                    | B -> unreachable "B never arrives"

                example pick
                    | "a" : (A) -> Answer(1)
                """;

        InputCaseEvidence input = input(claimed, 0);

        assertEquals(List.of(), input.excluded().stream().map(each -> each.name()).toList());
        assertEquals(List.of("B"), input.unspecified().stream().map(each -> each.name()).toList());
    }

    /**
     * A name is a position because of the binding it is, and not because of how it is spelled.
     *
     * <p>The local shadows the parameter and holds whatever the call answers with, so nothing here
     * says an {@code Off} arrives at it. Read by spelling, the arm is judged against the
     * parameter's rules — which admit one — and a model that says nothing wrong is refused.
     */
    @Test
    void aLocalThatShadowsAParameterIsNotTheParameter() {
        String shadowed = """
                module example.probe

                data On
                data Off
                data Flag = On | Off
                data Active = Flag invariant value /= Off
                data Answer = Int

                let defaulted (f: Flag): Active =
                    match f with
                        | On  -> Active(On)
                        | Off -> Active(On)

                behavior pick : (f: Flag) -> Answer
                    constructs Answer, Active, On

                let pick (f) = {
                    let f = defaulted(f)
                    match f.value with
                        | On  -> Answer(1)
                        | Off -> unreachable "a defaulted flag is never Off"
                }
                """;

        assertEquals(List.of(), errorsIn(shadowed), "nothing here is wrong");
    }

    /**
     * And a name bound to a position is that position, whatever it is called.
     *
     * <p>A helper expanded into a body binds the call's argument to its own parameter and matches
     * that. Read by spelling, this is caught only where the two happen to share a name — so the
     * helper's is deliberately not the behavior's here.
     */
    @Test
    void aClaimInsideAnExpandedHelperIsJudgedAgainstWhatTheCallGaveIt() {
        String throughHelper = """
                module example.probe

                data On
                data Off
                data Flag = On | Off
                data Answer = Int

                let decide (g: Flag): Answer =
                    match g with
                        | On  -> Answer(1)
                        | Off -> unreachable "the caller never passes Off"

                behavior pick : (f: Flag) -> Answer
                    constructs Answer

                let pick (f) = decide(f)
                """;

        assertEquals(List.of("E1326"), errorsIn(throughHelper));
    }

    /** The codes of whatever this model is refused for, in the order they are reported. */
    private static List<String> errorsIn(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        return compilation.db().allReports().stream()
                .filter(found -> found.report().isError())
                .map(found -> found.report().diagnostic().code())
                .toList();
    }

    /**
     * A claim about a position past the axis limit is still said.
     *
     * <p>Twelve positions are as many as a report draws axes at, and a claim about the thirteenth
     * had a verdict all the same. Left to the axes to print, that verdict is reached and dropped —
     * an exclusion both unproven and silent, one level up from where that was ruled out.
     */
    @Test
    void aClaimAboutAPositionPastTheAxisLimitIsSaid() {
        String wide = """
                module example.probe

                data On
                data Off
                data Pending
                data Flag = On | Off | Pending
                data Many =
                    { a: Bool, b: Bool, c: Bool, d: Bool, e: Bool, f: Bool, g: Bool
                    , h: Bool, i: Bool, j: Bool, k: Bool, l: Bool, m: Bool
                    }
                data T = { one: Flag, two: Flag } invariant one /= two
                data Answer = Int

                behavior pick : (many: Many, t: T) -> Answer
                    constructs Answer

                let pick (many, t) = match t.one with
                    | On      -> Answer(1)
                    | Pending -> Answer(0)
                    | Off     -> unreachable "the probe never passes Off"

                example pick
                    | "on" : (Many { a = true, b = true, c = true, d = true, e = true, f = true
                                   , g = true, h = true, i = true, j = true, k = true, l = true
                                   , m = true }, T { one = On, two = Off }) -> Answer(1)
                """;

        PartitionEvidence partition = partitionOf(wide);
        String report = reportOn(wide);

        assertTrue(partition.axes().stream().noneMatch(each -> each.path().equals("t.one")),
                () -> "the position is past the limit: "
                        + partition.axes().stream().map(each -> each.path()).toList());
        assertTrue(report.contains("`Off` at `t.one` is declared unreachable: "
                        + "the probe never passes Off"),
                () -> "the claim is named by its position:\n" + report);
    }

    /**
     * And so is one about a position deeper than the walk goes.
     *
     * <p>Two levels is as deep as a report reads into what a parameter holds. A claim below that is
     * about a position nothing was read about, which is what the verdict says — and saying it is
     * the whole difference from a claim quietly acted on.
     */
    @Test
    void aClaimBelowWhereTheWalkStopsIsSaid() {
        String deep = """
                module example.probe

                data On
                data Off
                data Flag = On | Off
                data Inner = { flag: Flag }
                data Middle = { inner: Inner }
                data Outer = { middle: Middle }
                data Answer = Int

                behavior pick : (o: Outer) -> Answer
                    constructs Answer

                let pick (o) = match o.middle.inner.flag with
                    | On  -> Answer(1)
                    | Off -> unreachable "the probe never passes Off"

                example pick
                    | "on" : (Outer { middle = Middle { inner = Inner { flag = On } } }) -> Answer(1)
                """;

        String report = reportOn(deep);

        assertTrue(partitionOf(deep).axes().isEmpty(),
                "nothing was read this far into the value");
        assertTrue(report.contains("`Off` at `o.middle.inner.flag` is declared unreachable: "
                        + "the probe never passes Off, and nothing here proves it: "
                        + "nothing was read about this case"),
                () -> "said where no axis carries it:\n" + report);
    }

    /**
     * A body says the same thing twice, and one case leaves the denominator once.
     *
     * <p>Two {@code match}es on one position, each with an arm for the case the rules refuse. What
     * left the count is one case however many arms declared it — counted per arm, the report said
     * {@code excluded 2} of a position with one case out of it — and each arm's words are kept.
     */
    @Test
    void aCaseTwoArmsDeclareLeavesTheDenominatorOnce() {
        String twice = """
                module example.probe

                data On
                data Off
                data Pending
                data Flag = On | Off | Pending
                data Active = Flag invariant value /= Off
                data Answer = Int

                behavior pick : (f: Active) -> Answer
                    constructs Answer

                let pick (f) = {
                    let first = match f.value with
                        | On      -> 1
                        | Pending -> 0
                        | Off     -> unreachable "an Active is never Off"
                    match f.value with
                        | On      -> Answer(first)
                        | Pending -> Answer(0)
                        | Off     -> unreachable "and it is never Off here either"
                }

                example pick
                    | "on" : (Active(On)) -> Answer(1)
                """;

        String report = reportOn(twice);

        assertTrue(report.contains("excluded 1"),
                () -> "one case is out of the denominator:\n" + report);
        assertTrue(report.contains("`Off` is declared unreachable on every path"),
                () -> "and both arms' words are kept:\n" + report);
    }

    /** The report a build reads, which is where a claim and a measure are put together. */
    private static String reportOn(String source) {
        return souther.compiler.report.AdequacyReport.of(measured(source))
                .human(SourceNameResolver.identity());
    }

    private static PartitionEvidence partitionOf(String source) {
        Compilation compilation = measured(source);
        PartitionEvidence partition = compilation.db()
                .ask(new Adequacy.Coverage(compilation.modules().get(0))).value().get("pick");
        assertNotNull(partition, "the model under test compiles");
        return partition;
    }

    /**
     * Several refusals arrive in the order the module declares them.
     *
     * <p>What a reader meets first is what they read first, and a file is read from the top. The
     * order is the module's and not the one a table of behaviors happened to iterate in — the names
     * here are spelled so that the two differ.
     */
    @Test
    void refusalsComeInTheOrderTheModuleDeclaresThem() {
        String three = """
                module example.probe

                data A
                data B
                data Kind = A | B
                data Answer = Int

                behavior zeta : (kz: Kind) -> Answer
                    constructs Answer

                let zeta (kz) = match kz with
                    | A -> Answer(1)
                    | B -> unreachable "zeta never sees B"

                behavior alpha : (ka: Kind) -> Answer
                    constructs Answer

                let alpha (ka) = match ka with
                    | A -> Answer(2)
                    | B -> unreachable "alpha never sees B"

                behavior mu : (km: Kind) -> Answer
                    constructs Answer

                let mu (km) = match km with
                    | A -> Answer(3)
                    | B -> unreachable "mu never sees B"
                """;

        assertEquals(List.of("E1326", "E1326", "E1326"), errorsIn(three));
        assertEquals(List.of("kz", "ka", "km"), positionsRefused(three),
                "read from the top, as a file is");
    }

    /** The position each refusal names, in the order the reports arrive. */
    private static List<String> positionsRefused(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        List<String> out = new ArrayList<>();
        for (Db.Found found : compilation.db().allReports()) {
            if (found.report().isError() && "E1326".equals(found.report().diagnostic().code())) {
                found.report().diagnostic().values().values().stream()
                        .map(String::valueOf).filter(each -> each.startsWith("k"))
                        .findFirst().ifPresent(out::add);
            }
        }
        return out;
    }

    /** The gap that is real is still reported; the one no row can fill is not. */
    @Test
    void theCaseWithAnAnswerIsStillOwedARow() {
        assertEquals(List.of("Pending"),
                input(RULED_OUT, 0).unspecified().stream().map(each -> each.name()).toList());
    }

    @Test
    void thePositionIsDividedIntoWhatARowCanBeWrittenAt() {
        PartitionEvidence.AxisCoverage axis = axis(RULED_OUT);

        assertEquals(List.of("On", "Pending"), axis.classes());
        assertEquals(List.of("Pending"), axis.uncovered());
        assertTrue(reportOn(RULED_OUT).contains("`Off` is declared unreachable"),
                () -> "and what the body said about the case it took out:\n"
                        + reportOn(RULED_OUT));
    }

    /** The model's own words, kept: what a report takes out of a denominator it has to be able to say
     * it took out, and why. */
    @Test
    void whyItIsRuledOutIsTheReasonTheModelWrote() {
        assertTrue(reportOn(RULED_OUT)
                        .contains("`Off` is declared unreachable: an Active is never Off"),
                () -> reportOn(RULED_OUT));
    }

    /**
     * A claim nothing settled leaves the case owed, and says that it did not settle it.
     *
     * <p>Both halves. What removes an obligation is a proof, so the case is counted; and what an
     * author needs beside the gap is that the model already declares the row cannot be written, and
     * that nothing here could tell whether that is so — an exclusion that is both unproven and
     * silent is the one an author cannot act on.
     */
    @Test
    void aClaimNothingSettledIsCountedAndSaid() {
        PartitionEvidence.AxisCoverage axis = axis(UNPROVEN, "t.f");
        String report = reportOn(UNPROVEN);

        assertEquals(List.of("On", "Off", "Pending"), axis.classes());
        assertFalse(report.contains("excluded"),
                () -> "nothing left the denominator:\n" + report);
        assertTrue(report.contains("`Off` is declared unreachable: the probe never passes Off,"
                        + " and nothing here proves it: a rule about this position went unread"),
                () -> report);
    }

    /**
     * A claim the model's own rules contradict is refused where it is written.
     *
     * <p>The one answer that is not a measure's. Nothing stands between the fork and the caller, so
     * `B` arrives whenever a caller passes one — and the arm says the model aborts there. What the
     * diagnostic names is the case, the position it arrives at, and the declaration that admits it.
     */
    @Test
    void aClaimTheRulesContradictIsRefused() {
        CompileException refused = org.junit.jupiter.api.Assertions.assertThrows(
                CompileException.class, () -> Compiler.compile("""
                        module example.probe

                        data A
                        data B
                        data Kind = A | B
                        data Answer = Int

                        behavior pick : (k: Kind) -> Answer
                            constructs Answer

                        let pick (k) = match k with
                            | A -> Answer(1)
                            | B -> unreachable "B never arrives"
                        """));

        assertEquals("E1326", refused.diagnostics().get(0).code(), refused.getMessage());
        assertTrue(refused.getMessage().contains("`B` can arrive at `k`"), refused.getMessage());
        assertTrue(refused.getMessage().contains("case of `Kind`"), refused.getMessage());
    }

    /**
     * A claim about a case that is written where a `let` binds is a claim at the first fork.
     *
     * <p>What a {@code let} binds runs before the body it binds it for, so this is the fork every
     * caller reaches. Read as a shape rather than as an order, the walk stepped over it to the end
     * of the spine and called a later fork the first one — and this claim, which the model's own
     * signature refutes, was never refused.
     */
    @Test
    void aForkWrittenAsABindingsValueIsStillTheFirstOne() {
        String bound = """
                module example.probe

                data A
                data B
                data Kind = A | B
                data Answer = Int

                behavior pick : (k: Kind) -> Answer
                    constructs Answer

                let pick (k) = {
                    let n = match k with
                        | A -> 1
                        | B -> unreachable "B never arrives"
                    Answer(n)
                }
                """;

        assertEquals(List.of("E1326"), errorsIn(bound));
    }

    /**
     * The reasons on the path that aborts, and nothing written past where it stops.
     *
     * <p>A construction whose first field aborts never evaluates the second, so a second
     * {@code unreachable} below it is text that never runs rather than a reason the value did not
     * arrive. Which one is first is the order the fields are declared and not the order the
     * initializers are written — the emitter walks the declaration and picks each field's
     * initializer out — so the two are written against each other here. Paths a fork keeps apart are
     * another matter: each of them is a way this arm answers nothing, so each is named.
     */
    @Test
    void theReasonsAreTheOnesEvaluationReaches() {
        String sequential = """
                module example.probe

                data On
                data Off
                data Flag = On | Off
                data Active = Flag invariant value /= Off
                data Answer = Int
                data Boxed = { a: Answer, b: Answer }

                behavior pick : (f: Active) -> Answer
                    constructs Answer, Boxed

                let pick (f) = match f.value with
                    | On  -> Answer(1)
                    | Off -> Boxed { b = unreachable "written first and evaluated second"
                                   , a = unreachable "declared first, so this is where it stops"
                                   }.a

                example pick
                    | "on" : (Active(On)) -> Answer(1)
                """;

        assertEquals(List.of("declared first, so this is where it stops"),
                reasonsSaidAbout(sequential, "Off"));

        String forked = """
                module example.probe

                data On
                data Off
                data Flag = On | Off
                data Active = Flag invariant value /= Off
                data Yes
                data No
                data Mark = Yes | No
                data Answer = Int

                behavior pick : (f: Active, m: Mark) -> Answer
                    constructs Answer

                let pick (f, m) = match f.value with
                    | On  -> Answer(1)
                    | Off -> match m with
                                 | Yes -> unreachable "not a marked Off"
                                 | No  -> unreachable "nor an unmarked one"

                example pick
                    | "on" : (Active(On), Yes) -> Answer(1)
                """;

        assertEquals(List.of("not a marked Off", "nor an unmarked one"),
                reasonsSaidAbout(forked, "Off"),
                "both arms are ways this arm answers nothing");
    }

    /** What the body wrote about one case, as the report carries it. */
    private static List<String> reasonsSaidAbout(String source, String named) {
        Compilation compilation = measured(source);
        return compilation.db()
                .ask(new souther.compiler.query.Bodies.Claimed(compilation.modules().get(0)))
                .value().get("pick").all().stream()
                .filter(each -> each.classId().equals(named))
                .findFirst().orElseThrow().reasons();
    }

    /**
     * A warning an author cannot act on is worse than no warning.
     *
     * <p>E1915 asks for a row at an input case and E1918 for a row through an arm. Both are warned
     * about here and both are about {@code Pending}, which is a row that can be written; neither is
     * about {@code Off}, which is not.
     */
    @Test
    void nothingIsWarnedAboutThatNoRowCouldAnswer() {
        assertEquals(List.of("E1915", "E1918"), warnings(RULED_OUT).stream().sorted().toList());
        assertTrue(messages(RULED_OUT).stream().allMatch(said -> said.contains("Pending")),
                messages(RULED_OUT).toString());
        assertFalse(messages(RULED_OUT).stream().anyMatch(said -> said.contains("Off")),
                messages(RULED_OUT).toString());
    }

    private static List<String> warnings(String source) {
        return reported(source).stream().map(d -> d.code()).toList();
    }

    /** What each warning is about, read off its arguments: the rendered text is the catalog's and
     * this is about which case was named. */
    private static List<String> messages(String source) {
        return reported(source).stream()
                .map(d -> d.values().values().stream().map(String::valueOf)
                        .collect(java.util.stream.Collectors.joining(" ")))
                .toList();
    }

    private static List<Diagnostic> reported(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.warningsAt(Adequacy.Level.ALL));
        compilation.answerEverything();
        List<Diagnostic> out = new ArrayList<>();
        for (Db.Found found : compilation.db().allReports()) {
            Diagnostic d = found.report().diagnostic();
            if (!found.report().isError() && d.code() != null && d.code().startsWith("E19")) {
                out.add(d);
            }
        }
        return out;
    }

    /**
     * What the generator offers has to be what the compiler accepts.
     *
     * <p>The row it used to write for {@code Off} was E1911 the moment it was uncommented: the tool
     * handing an author work its own compiler refuses. Checked by writing the rows out, answering
     * them and compiling — a generator that offered nothing at all would pass an assertion about
     * {@code Off} alone, so what it does offer is fixed as well.
     */
    @Test
    void everyRowTheGeneratorOffersCompiles() {
        String offered = GeneratedRows.of(measured(RULED_OUT), "example.probe", "pick", false,
                SourceNameResolver.identity());

        assertTrue(offered.contains("(Pending)"), offered);
        assertFalse(offered.contains("(Off)"), offered);

        String answered = RULED_OUT + "\n" + uncommented(offered).replace("<?>", "Answer(0)");
        Compilation amended = Compilation.ofSource(answered, "Main");
        amended.answerEverything();
        assertEquals(List.of(), amended.db().allReports().stream()
                .filter(found -> found.report().isError())
                .map(found -> found.report().diagnostic().code()).toList(), answered);
    }

    /** The rows out of a generated block, with the comment marker each is offered behind removed. */
    private static String uncommented(String offered) {
        StringBuilder out = new StringBuilder();
        for (String line : offered.split("\n")) {
            if (line.startsWith("// example") || line.startsWith("//     |")) {
                out.append(line.substring(3)).append('\n');
            }
        }
        return out.toString();
    }

    /**
     * A step handed to a combinator is not the arm running it.
     *
     * <p>Evaluating the position a function is written in makes the function; its body runs when the
     * call applies it, on arguments this position does not have — a step that aborts on an element it
     * may never be handed is not the arm failing to answer. Read the other way round, the arm holding
     * the call is not an arm, and the case in front of it leaves the denominator: a class rows do sit
     * in, and here a row sits in it.
     *
     * <p>Checked through the measures rather than on the predicate alone, because what the mistake
     * costs is downstream of it: the row for {@code Off} is written, runs and holds, and the report
     * used to say the position had one class and two rows specified at it.
     */
    @Test
    void aStepThatAbortsDoesNotRuleOutTheCaseThatPassesItAlong() {
        String higher = """
                module example.probe

                data On
                data Off
                data Flag = On | Off
                data Answer = Int

                behavior pick : (f: Flag, xs: List<Int>) -> Answer
                    constructs Answer

                let pick (f, xs) = match f with
                    | On  -> Answer(1)
                    | Off -> Answer(List.fold(
                                 (acc, x) -> Answer(unreachable "no element arrives").value, 0, xs))

                example pick
                    | "on"  : (On, [1]) -> Answer(1)
                    | "off" : (Off, []) -> Answer(0)
                """;

        assertEquals(List.of(), input(higher, 0).excluded().stream().toList());
        assertEquals(2, input(higher, 0).coverable().size());
        assertEquals(List.of(), input(higher, 0).unspecified().stream().toList());
        assertEquals(List.of("On", "Off"), axis(higher).classes());
        assertEquals(List.of(), axis(higher).uncovered());
    }

    /**
     * A binding before the fork does not hide it.
     *
     * <p>What a {@code let} binds is evaluated on the way to the answer and is not a fork, so the
     * {@code match} below it is still the first fork this body has.
     */
    @Test
    void aBindingBeforeTheForkIsSteppedOver() {
        String bound = """
                module example.probe

                data On
                data Off
                data Flag = On | Off
                data Active = Flag invariant value /= Off
                data Answer = Int

                behavior pick : (f: Active) -> Answer
                    constructs Answer

                let pick (f) = {
                    let one = 1
                    match f.value with
                        | On  -> Answer(one)
                        | Off -> unreachable "the probe never passes Off"
                }

                example pick
                    | "on" : (Active(On)) -> Answer(1)
                """;

        assertEquals(List.of("the probe never passes Off"), reasonsSaidAbout(bound, "Off"));
    }

    /**
     * Nothing is read off a condition.
     *
     * <p>Which values satisfy a predicate is what a solver answers, and a wrong answer here takes a
     * case out of the report that an author should have been asked about. The case stays in, and the
     * gap it leaves is reported as the gap it is.
     */
    @Test
    void aCaseRuledOutByAConditionIsNotReadAsRuledOut() {
        String guarded = """
                module example.probe

                data On
                data Off
                data Flag = On | Off
                data Answer = Int

                behavior pick : (f: Flag, senior: Bool) -> Answer
                    constructs Answer

                let pick (f, senior) =
                    if senior then unreachable "no senior reaches this" else Answer(1)

                example pick
                    | "on" : (On, false) -> Answer(1)
                """;

        assertEquals(List.of(), input(guarded, 0).excluded().stream().toList());
        assertEquals(List.of("Off"),
                input(guarded, 0).unspecified().stream().map(each -> each.name()).toList());
    }

    /**
     * An exclusion under a fork is not lifted out of it.
     *
     * <p>An arm of one {@code match} holding a {@code match} on another parameter says what that
     * parameter cannot be <em>given the first one</em>. Read as a fact about the parameter it would
     * remove a case that other arms do answer for.
     */
    @Test
    void anExclusionThatHoldsOnlyUnderAnotherCaseIsNotReadAsHoldingEverywhere() {
        String nested = """
                module example.probe

                data On
                data Off
                data Flag = On | Off
                data Yes
                data No
                data Mark = Yes | No
                data Answer = Int

                behavior pick : (f: Flag, m: Mark) -> Answer
                    constructs Answer

                let pick (f, m) = match f with
                    | On  -> match m with
                                 | Yes -> Answer(1)
                                 | No  -> unreachable "no unmarked On arrives"
                    | Off -> Answer(0)

                example pick
                    | "on" : (On, Yes) -> Answer(1)
                """;

        assertEquals(List.of(), input(nested, 1).excluded().stream().toList(),
                "`No` is answered when `f` is `Off`");
        assertEquals(List.of("No"),
                input(nested, 1).unspecified().stream().map(each -> each.name()).toList());
    }

    /** And the arm inside is still not an arm: what the body does not answer for is not a fork a row
     * takes, wherever it is written. */
    @Test
    void theArmUnderTheForkIsStillNotAnArm() {
        CompileException refused = org.junit.jupiter.api.Assertions.assertThrows(
                CompileException.class, () -> Compiler.compile(UNPROVEN + """
                            | "off" : (T { f = Off, g = On }) -> Answer(0)
                        """));

        assertEquals("E1911", refused.diagnostics().get(0).code(), refused.getMessage());
    }
}
