package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.check.Prepared;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.NameReach;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Requirements;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.query.Compilation;
import souther.compiler.query.Shapes;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where a row writes to move a number is a place the reading answered for, reached by following the
 * name through whatever crossings stand between.
 *
 * <p>Two things have to hold and neither follows from the other. A path the reading never reached is
 * one no row may be written at, however ordinary it looks: what says so is what the declarations
 * came to there, and where a name stands cannot — a name that crosses nothing is at a position and
 * at a path deeper than the reading goes alike. And a name that crosses is followed until it reaches
 * a place that was answered for, because a name under two sums is one crossing from a name that is
 * still one crossing from a position.
 */
class ANumberIsWrittenWhereTheReadingAnsweredForThePlaceTest {

    /**
     * A model with a number no measure of this behavior is about: nothing divides the chain, so the
     * measurement worked nothing out at its end while the declarations still say what is there.
     */
    private static final String UNMEASURED = """
            module example.unmeasured

            data L3 = { held: Int }
            data L2 = { under: L3 }
            data L1 = { inside: L2 }

            data Ok
            data No

            behavior read : (o: L1, n: Int) -> Ok | No

            let read (o, n) = {
                guard n > 3 else No
                Ok
            }
            """;

    /** Two sums on the way down, so that a name crossing both is one crossing from a name that
     *  crosses again. */
    private static final String NESTED = """
            module example.nested

            data Inner = { deep: Int }
            data IA = { ...Inner, p: Int }
            data IB = { ...Inner, r: Int }
            data IS = IA | IB

            data Outer = { s: IS }
            data OA = { ...Outer, m: Int }
            data OB = { ...Outer, n: Int }
            data OS = OA | OB

            data Ok
            data No

            behavior read : (q: OS, n: Int) -> Ok | No

            let read (q, n) = {
                guard n > 3 else No
                guard q.s.deep > 10 else No
                Ok
            }
            """;

    /**
     * A condition over a place this measurement worked nothing out about composes no row.
     *
     * <p>The place looks like any other to a reader of where names stand: nothing crosses there.
     * And it is writable — the traversal that follows a value reaches a number at it, so a row
     * would be written if anything here were entitled to write one. Nothing is: a value offered
     * there would stand at a place this compiler never worked out what holds, which is the row
     * {@link AdmittedValues} exists to keep out of an author's hands.
     *
     * <p>Which is a state only what was worked out can report. Sorted by where the name stands,
     * this place and a position the measurement answered for are one answer — and the second may be
     * written at.
     *
     * <p>What the attempt does about it is say so and go on. A condition nothing could be placed
     * under is carried out with the row rather than refusing it ({@code CompositionAccount}), so
     * what is asserted is the account: the composer put no value under the condition, which is the
     * whole of what declining to write there comes to.
     *
     * <p><b>The condition is written here and not read off a body.</b> What this establishes is what
     * the composer does with one, and not that some body's reading hands it one — the three lines
     * above are what say the place is reachable and writable, and whether a condition ever arrives
     * over such a place is a question about readings and belongs to whoever asks it.
     */
    @Test
    void aConditionOverAPlaceNothingWorkedOutHasNoValuePutUnderIt() {
        TermPath unmeasured = TermPath.of("o").then("inside").then("under").then("held");

        assertEquals(new AdmittedValues.Admitted.NotWorkedOut(),
                subject(UNMEASURED).witnessSearch().admitted().at(unmeasured));
        assertInstanceOf(NameReach.Standing.AtThePathItself.class,
                domain(UNMEASURED).reach().standingOf(unmeasured),
                "and nothing crosses there, which is what a place the measurement answered for"
                        + " says as well");
        assertNotNull(subject(UNMEASURED).inputs().typeAtWrittenPath(unmeasured),
                "and a value written there would go somewhere, so what keeps a value out is what"
                        + " was worked out and not what can be written");

        Generator.BoundaryAttempt attempt = composing(UNMEASURED, unmeasured);

        assertEquals(List.of(new ReachabilityGap.Uncomposed(
                        onTheWayOver(unmeasured),
                        new ReachabilityGap.Why.NoValueComposedForItsPositions())),
                attempt.unrepresented().onTheWay(),
                "nothing is placed at a place nothing worked out, and the attempt says so: "
                        + attempt.unrepresented());
    }

    /**
     * A condition over a name two sums down is written at a position the reading has.
     *
     * <p>The name is followed one crossing at a time, which is how the sorting answers, until it
     * reaches a place that was answered for. Stopping at the first answer leaves a name that still
     * crosses, and a row written there would go to the inner sum's own name — so the composer would
     * report a condition over a name the model puts four positions under as one nothing could put a
     * value under.
     */
    @Test
    void aConditionOverANameTwoSumsDownIsWrittenWhereTheReadingHasIt() {
        InputDomain read = domain(NESTED);
        TermPath shared = TermPath.of("q").then("s").then("deep");

        assertNull(read.at(shared), "the name is at the sum and the positions are under the cases");

        Generator.BoundaryAttempt attempt = composing(NESTED, shared);

        assertEquals(List.of(), attempt.unrepresented().onTheWay(),
                "the composer put a value under the condition, which is what following the name to"
                        + " a position it stands at comes to: " + attempt.unrepresented());
        Generator.BoundaryAttempt.Built built = assertInstanceOf(
                Generator.BoundaryAttempt.Built.class, attempt,
                "and the row is written: " + attempt);
        assertTrue(written(built).stream().anyMatch(each -> each.startsWith("OA ")),
                "under the first case at each sum, which is where the value was placed: "
                        + written(built));
    }

    /** The values one row writes, as a person reads them. */
    private static List<String> written(Generator.BoundaryAttempt.Built built) {
        return built.row().inputs().stream().map(FixtureTemplate::text).toList();
    }

    /** Which question a report about the condition under test would put. */
    private static final ConditionReportAnchor WHERE =
            new ConditionReportAnchor.WhereTheReadingMetIt("m",
                    new ConditionOccurrence("b", 0));

    /** The condition the row is composed under, which a report about it would be the subject of. */
    private static OnTheWay.TakenIn onTheWayOver(TermPath at) {
        return new OnTheWay.TakenIn(WHERE, new TakenConstraint.Affine(
                LinearForm.atom(new NumericTerm.ValueOf(at)), Rel.GE));
    }

    /** A row composed with the plain position fixed, and a condition over {@code at} on the way to
     *  it. */
    private static Generator.BoundaryAttempt composing(String source, TermPath at) {
        MeasuredInput subject = subject(source);
        Axis fixed = axisAt(source, "n");
        Count four = Count.of(4);
        return Generator.probeFixing(subject, "n = 4",
                Map.of(new RealizationTarget.AtOnePosition(fixed.term()), four),
                NumbersAskedFor.of(LevelRegion.point(new Level.OnACarrier(
                        quantities(source).ordersOf(fixed.term()).answered(), four))),
                new Reachability.Reaching(quantities(source).region(), Requirements.NONE,
                        List.of(onTheWayOver(at))),
                Generator.CandidateCheck.ANY);
    }

    // Each model is read once and answered from.
    private static final Map<String, Compilation> COMPILED = new java.util.HashMap<>();

    private static synchronized Compilation compiled(String source) {
        return COMPILED.computeIfAbsent(source, each -> {
            Compilation made = Compilation.ofSource(each, "Main");
            // Measured, because the lines a row is composed at are drawn where a behavior is.
            made.measure(souther.compiler.query.Adequacy.Asked.fullReport());
            made.answerEverything();
            return made;
        });
    }

    private static String module(String source) {
        return compiled(source).modules().get(0);
    }

    private static RuleReadingSource rules(String source) {
        return RuleReadings.of(compiled(source), module(source));
    }

    private static Hir.SpecBehavior spec(String source) {
        Prepared prepared = compiled(source).db()
                .ask(new Shapes.Prepared(module(source))).value();
        return (Hir.SpecBehavior) prepared.behaviors().stream()
                .filter(each -> each.name().equals("read")).findFirst().orElseThrow();
    }

    private static InputDomain domain(String source) {
        InputDomain read = compiled(source).db()
                .ask(new souther.compiler.query.Adequacy.Inputs(module(source))).value()
                .get(spec(source).name());
        assertNotNull(read, "the model under test compiles");
        return read;
    }

    private static souther.compiler.inputs.Quantities quantities(String source) {
        return domain(source).quantities(rules(source));
    }

    private static List<Axis> axes(String source) {
        return compiled(source).db()
                .ask(new souther.compiler.query.Adequacy.Divided(module(source),
                        spec(source).name()))
                .value().axes();
    }

    private static Axis axisAt(String source, String path) {
        return axes(source).stream().filter(each -> each.path().toString().equals(path))
                .findFirst().orElseThrow(() -> new IllegalStateException(
                        "the model under test is measured at " + path));
    }

    private static MeasuredInput subject(String source) {
        return MeasuredInput.of(spec(source).name(), domain(source).reading(rules(source)),
                AxesATestWrote.asAMeasurement(spec(source).name(), axes(source)));
    }
}
