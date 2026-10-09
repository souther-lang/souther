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
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.Shapes;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A case the row cannot be beside what it already is is not a way of writing a number of that row,
 * and it leaves nothing open about the cut.
 *
 * <p>{@code r.deadline} is spread by both cases of {@code Req}, and the way to the point already
 * has the row be a {@code P}. A {@code P} holds its deadline to five, so a cut asking for one above
 * ten leaves the row nothing — and the {@code T} beside it is not a way the search left unlooked
 * at, because no value is a {@code P} and a {@code T} at once. The cut is the rules leaving nothing,
 * which is the model's word, and not a cut this compiler did not get to the end of.
 */
class ACaseTheRowCannotBeIsNoWayOfWritingItTest {

    private static final String SPREAD = """
            module example.spread

            data Base = { deadline: Int }
                invariant deadline >= 0 && deadline <= 100
            data P = { ...Base }
                invariant deadline <= 5
            data T = { ...Base }
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

    private static final TermPath DEADLINE = TermPath.of("r").then("deadline");

    /** {@code r.deadline - 11 >= 0}. */
    private static final TakenConstraint ABOVE_TEN = new TakenConstraint.Affine(
            LinearForm.atomMinusConstant(new NumericTerm.ValueOf(DEADLINE), ExactRatio.of(11)),
            Rel.GE);

    @Test
    void underACaseThatLeavesTheCutNothingTheRulesAreSaidToLeaveNothing() {
        Generator.BoundaryAttempt.Unresolved unresolved = assertInstanceOf(
                Generator.BoundaryAttempt.Unresolved.class, composing(rowIsA("P")));

        assertEquals(Generator.UnresolvedCombination.Reason.THE_RULES_LEAVE_NOTHING_THERE,
                unresolved.why().reason(), unresolved.toString());
    }

    /** The control: a row that is not yet anything is written under the case that takes the cut. */
    @Test
    void aRowThatIsNotYetACaseIsWrittenUnderTheOneThatTakesIt() {
        assertInstanceOf(Generator.BoundaryAttempt.Built.class, composing(Requirements.NONE));
    }

    /** What a row has to be to be the case named {@code name}, as the reading of the sum says it. */
    private static Requirements rowIsA(String name) {
        NameReach.Standing.UnderTheCases under = assertInstanceOf(
                NameReach.Standing.UnderTheCases.class, domain().reach().standingOf(DEADLINE));
        return under.standings().stream()
                .filter(each -> each.position().toString().contains("@" + name + "."))
                .findFirst().orElseThrow().assuming();
    }

    /** A row with {@code n} at four, reached by a way that takes the cut in and requires
     *  {@code required}. */
    private static Generator.BoundaryAttempt composing(Requirements required) {
        Axis fixed = axisAt("n");
        Count at = Count.of(4);
        SearchRegion region = domain().quantities(rules()).region();
        if (ABOVE_TEN instanceof TakenConstraint.Affine(var form, var rel)) {
            region = region.assuming(form, rel).taken();
        }
        return Generator.probeFixing(subject(), "n = " + at,
                Map.of(new RealizationTarget.AtOnePosition(fixed.term()), at),
                NumbersAskedFor.of(LevelRegion.point(new Level.OnACarrier(
                        domain().quantities(rules()).ordersOf(fixed.term()).answered(), at))),
                new Reachability.Reaching(region, required, TruthsAsked.NONE,
                        List.of(new OnTheWay.TakenIn(new ConditionReportAnchor.WhereTheReadingMetIt(
                                "m", new ConditionOccurrence("b", 0)),
                                new RowDemand.Relational(ABOVE_TEN))), List.of()),
                Generator.CandidateCheck.ANY);
    }

    private static final Compilation COMPILATION = compiled();

    private static Compilation compiled() {
        Compilation made = Compilation.ofSource(SPREAD, "Main");
        made.measure(Adequacy.Asked.fullReport());
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
        InputDomain read = COMPILATION.db().ask(new Adequacy.Inputs(module())).value()
                .get(spec().name());
        assertNotNull(read, "the model under test compiles");
        return read;
    }

    private static List<Axis> axes() {
        return COMPILATION.db().ask(new Adequacy.Divided(module(), spec().name())).value().axes();
    }

    private static MeasuredInput subject() {
        return MeasuredInput.of(spec().name(), domain().reading(rules()),
                AxesATestWrote.asAMeasurement(spec().name(), axes()));
    }

    private static Axis axisAt(String path) {
        return axes().stream().filter(each -> each.path().toString().equals(path)).findFirst()
                .orElseThrow();
    }
}
