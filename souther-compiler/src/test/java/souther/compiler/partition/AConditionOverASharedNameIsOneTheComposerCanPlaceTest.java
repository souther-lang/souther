package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.ast.Hir;
import souther.compiler.check.Prepared;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Requirements;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.query.Compilation;
import souther.compiler.query.Shapes;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A condition above a line over a name every case of a sum spreads is one the composer has an order
 * for.
 *
 * <p>The generator's side of what the reading answers. {@code r.deadline} is a name a value of the
 * sum is read at: the reading has no position there because it goes under each case, and the
 * traversal that follows a written value has nothing there because a row writes one of the cases. A
 * composer that took the order from the second would report a condition it was handed as one nothing
 * could put a value under — the reachability was stated, and the answer would be that there is no
 * order for it.
 *
 * <p>So the condition is placed and the row is written under one of the cases. Where a row writes to
 * move a number is where the number is read for every number but this one, and a composer that took
 * the second for the first would write at the sum's own name — which is nowhere, and came back as a
 * row nothing could compose a value for.
 */
class AConditionOverASharedNameIsOneTheComposerCanPlaceTest {

    private static final String SPREAD = """
            module example.spread

            data Base = { deadline: Int }
            data P = { ...Base, x: Int }
            data T = { ...Base, y: Int }
            data Req = P | T

            data Ok
            data No

            behavior check : (r: Req, n: Int) -> Ok | No

            let check (r, n) = {
                guard n > 3 else No
                guard r.deadline > 10 else No
                Ok
            }
            """;

    /** The name every case spreads, which the reading has no position at. */
    private static final TermPath DEADLINE = TermPath.of("r").then("deadline");

    /** The reading has no position there, and no axis stands at it either — which is what sends the
     *  question to whatever the composer holds. */
    @Test
    void nothingStandsAtTheSharedNameToBeAskedInstead() {
        assertNull(domain().at(DEADLINE),
                "the reading goes under each case, so the shared name holds no position");
        assertEquals(List.of(), axes().stream()
                        .filter(each -> each.path().equals(DEADLINE)).toList(),
                "and no axis stands there to be asked in its place");
    }

    /**
     * The composer places the way's position and the row writes the value under one of the cases.
     *
     * <p>Asking the traversal that follows a written value instead answers that there is nowhere to
     * write the number, which is a row refused for something that is not the case: the value stands
     * under whichever case the row is, and a row that is one of them holds it.
     */
    @Test
    void aConditionOverTheSharedNameIsPlacedAndTheRowIsWrittenUnderACase() {
        Generator.BoundaryAttempt attempt = composing(Count.of(4), ANYWHERE_ON_THE_ORDER);

        assertEquals(List.of(), attempt.unrepresented().onTheWay(),
                "the composer had an order for the name every case spreads: "
                        + attempt.unrepresented());
        Generator.BoundaryAttempt.Built built = assertInstanceOf(
                Generator.BoundaryAttempt.Built.class, attempt,
                "a value stands at the name under a case, so the row is written: " + attempt);
        assertTrue(written(built).stream().anyMatch(each -> each.startsWith("P ")),
                "and the row writes one of the cases the name is spread by: " + written(built));
    }

    /**
     * And the row writes the shared name once, where the case holds it.
     *
     * <p>Beside the one above rather than folded into it. That one says a row was written at all;
     * this one says the value went to the name the condition was about — a routing that wrote a
     * case with nothing at the shared name would leave the condition standing over a name the row
     * says nothing about.
     */
    @Test
    void theRowHoldsAValueAtTheNameTheConditionWasAbout() {
        Generator.BoundaryAttempt.Built built = assertInstanceOf(
                Generator.BoundaryAttempt.Built.class,
                composing(Count.of(4), ANYWHERE_ON_THE_ORDER));

        assertEquals(1, written(built).stream()
                        .filter(each -> each.contains("deadline =")).count(),
                "the row writes the name the cases share, once: " + written(built));
    }

    /**
     * What a search is told of the shared name is that the values stand under the cases, and not
     * that the declarations leave it everything.
     *
     * <p>The two narrow the same amount and say unlike things. Read as a set of every value, the
     * declarations would be answering for a position they were never asked about — and the search
     * that writes a value would have nothing left to tell it the row goes under a case.
     */
    @Test
    void theSearchIsToldTheValuesStandUnderTheCasesAndNotThatEveryOneIsAdmitted() {
        AdmittedValues admitted = subject().witnessSearch().admitted();

        assertEquals(new AdmittedValues.Admitted.StandsUnderTheCases(), admitted.at(DEADLINE));
        assertInstanceOf(AdmittedValues.Admitted.Values.class,
                admitted.at(domain().reach().crossings().get(0).to()),
                "and under the case the declarations do answer, which is what makes the answer"
                        + " above a state of its own");
    }

    /** The values one row writes, as a person reads them. */
    private static List<String> written(Generator.BoundaryAttempt.Built built) {
        return built.row().inputs().stream().map(FixtureTemplate::text).toList();
    }

    /** Which question a report about the condition under test would put. */
    private static final ConditionReportAnchor WHERE =
            new ConditionReportAnchor.WhereTheReadingMetIt("m",
                    new ConditionOccurrence("b", 0));

    /** A row composed with the plain position fixed at {@code at}, and {@code taken} over the
     *  shared name on the way to it. */
    private static Generator.BoundaryAttempt composing(Count at, TakenConstraint taken) {
        Axis fixed = axisAt("n");
        return Generator.probeFixing(subject(), "n = " + at,
                Map.of(new RealizationTarget.AtOnePosition(fixed.term()), at),
                NumbersAskedFor.of(LevelRegion.point(new Level.OnACarrier(
                        domain().quantities(rules()).ordersOf(fixed.term()).answered(), at))),
                new Reachability.Reaching(domain().quantities(rules()).region(),
                        Requirements.NONE,
                        List.of(new OnTheWay.TakenIn(WHERE, taken))),
                Generator.CandidateCheck.ANY);
    }

    /** {@code r.deadline >= 0}, which every value of the case meets. */
    private static final TakenConstraint ANYWHERE_ON_THE_ORDER = new TakenConstraint.Affine(
            LinearForm.atom(new NumericTerm.ValueOf(DEADLINE)), Rel.GE);

    // The compilation, read once and answered from.
    private static final Compilation COMPILATION = compiled();

    private static Compilation compiled() {
        Compilation made = Compilation.ofSource(SPREAD, "Main");
        // Measured, because the lines under test are drawn by the body: what the declarations alone
        // divide is the sum's cases, and a guard is read where a behavior is measured.
        made.measure(souther.compiler.query.Adequacy.Asked.fullReport());
        made.answerEverything();
        return made;
    }

    private static String module() {
        return COMPILATION.modules().get(0);
    }

    private static RuleReadingSource rules() {
        return RuleReadings.of(COMPILATION, module());
    }

    private static Hir.SpecBehavior spec() {
        Prepared prepared = COMPILATION.db().ask(new Shapes.Prepared(module())).value();
        return (Hir.SpecBehavior) prepared.behaviors().stream()
                .filter(each -> each.name().equals("check")).findFirst().orElseThrow();
    }

    private static InputDomain domain() {
        InputDomain read = COMPILATION.db()
                .ask(new souther.compiler.query.Adequacy.Inputs(module())).value()
                .get(spec().name());
        assertNotNull(read, "the model under test compiles");
        return read;
    }

    /** The measures of this behavior as the phase that generates rows has them, which is where the
     *  body's guards are read. */
    private static List<Axis> axes() {
        return COMPILATION.db()
                .ask(new souther.compiler.query.Adequacy.Divided(module(), spec().name()))
                .value().axes();
    }

    private static Axis axisAt(String path) {
        return axes().stream().filter(each -> each.path().toString().equals(path))
                .findFirst().orElseThrow(() -> new IllegalStateException(
                        "the model under test is measured at " + path + ", and this run has "
                                + axes().stream().map(each -> each.id().toString()).toList()));
    }

    private static MeasuredInput subject() {
        List<String> names = new ArrayList<>();
        spec().params().forEach(each -> names.add(each.name()));
        assertTrue(names.contains("n"), "the model takes the position the row is fixed at");
        return MeasuredInput.of(spec().name(), domain().reading(rules()),
                AxesATestWrote.asAMeasurement(spec().name(), axes()));
    }
}
