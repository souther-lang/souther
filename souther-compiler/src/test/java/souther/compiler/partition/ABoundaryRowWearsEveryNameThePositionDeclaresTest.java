package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeChecker;
import souther.compiler.core.Core;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.Shapes;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A row at a boundary is written wearing every name its position declares.
 *
 * <p>Two questions meet at a boundary row and only one of them is the carrier's. What a count is
 * written as — a number, an ISO date, a case name — is the carrier's; how many names that value
 * wears on the way to the position is the position's, and a newtype over a newtype wears two. Asked
 * of the carrier as well, the second was answered one layer deep, and the row came back missing the
 * name in the middle for the decoder to refuse.
 *
 * <p>Held here rather than left to the corpus: no example declares a newtype over a newtype, so
 * nothing measured would have said this stopped working.
 */
class ABoundaryRowWearsEveryNameThePositionDeclaresTest {

    @Test
    void aTemporalBoundaryUnderTwoNamesWearsBoth() {
        assertEquals(List.of("AT -> ShippingDay(Day(Date(\"2026-08-01\")))",
                        "BELOW -> ShippingDay(Day(Date(\"2026-07-31\")))"),
                rowsAtBoundaries("""
                        module example.nesteddate

                        data Day = Date
                        data ShippingDay = Day

                        data Ok
                        data No
                        data Verdict = Ok | No

                        behavior f : (d: ShippingDay) -> Verdict
                            constructs Ok, No
                        let f (d) = { guard d.value.value < Date("2026-08-01") else Ok
                            No }
                        """));
    }

    /** The same of a number, which was one layer deep before any of this and is not any more. */
    @Test
    void aNumericBoundaryUnderTwoNamesWearsBoth() {
        assertEquals(List.of("AT -> ShippingAmount(Amount(500))",
                        "BELOW -> ShippingAmount(Amount(499))"),
                rowsAtBoundaries("""
                        module example.nestedint

                        data Amount = Int
                        data ShippingAmount = Amount

                        data Ok
                        data No
                        data Verdict = Ok | No

                        behavior f : (a: ShippingAmount) -> Verdict
                            constructs Ok, No
                        let f (a) = { guard a.value.value < 500 else Ok
                            No }
                        """));
    }

    /** What a row carries at each boundary of the one behavior in {@code source}. */
    private static List<String> rowsAtBoundaries(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Hir.Module prepared = compilation.db().ask(new Shapes.Prepared(module)).value();
        Symbols symbols = compilation.db().ask(new Shapes.Scope(module)).value();
        Map<String, Sig> sigs = compilation.db().ask(new Bodies.Signatures(module)).value();
        TypeChecker.Checked checked = compilation.db().ask(new Bodies.Checked(module)).value();
        assertNotNull(checked, "the model under test compiles");

        Hir.SpecBehavior spec = (Hir.SpecBehavior) prepared.behaviors().get(0);
        Core body = checked.behaviorBodies().get(spec.name());
        CoverageSites.Plan plan = CoverageSites.of("m.sou", checked.behaviorBodies());
        GuardThresholds.Guards guards = GuardThresholds.of(spec.name(), body, plan,
                spec.params().stream().map(Hir.Param::name).toList(), symbols);
        Partitions.Partitioning p = Partitions.withThresholds(
                Partitions.of(spec, sigs.get(spec.name()), symbols, Exclusions.NONE),
                guards.thresholds(), symbols);

        List<String> names = new ArrayList<>();
        spec.params().forEach(each -> names.add(each.name()));
        Generator.Subject subject = new Generator.Subject(
                new BehaviorInputs(names, sigs.get(spec.name()).inputTypes(), symbols), p.axes());

        List<String> out = new ArrayList<>();
        for (Axis axis : p.axes()) {
            for (BoundaryObligation each
                    : Partitions.obligationsOf(axis, symbols, p.domains().get(axis.term()))) {
                out.add(each.side() + " -> "
                        + (Generator.probe(subject, each, Generator.CandidateCheck.ANY)
                                instanceof Generator.BoundaryAttempt.Built built
                                        ? String.join(", ", built.row().inputs().stream()
                                                .map(FixtureTemplate::text).toList())
                                        : "no row"));
            }
        }
        return out;
    }
}
