package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Ast;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeChecker;
import souther.compiler.core.Core;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.observe.ObservedValue;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.Shapes;

import java.math.BigDecimal;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The lines a behavior's own comparisons draw through its inputs.
 *
 * <p>This is where a numeric position stops being one undivided range. "Pre-approval above a hundred
 * thousand" is in no type — it is the comparison the body makes — and it is the line the rows have to
 * be written on both sides of.
 */
class ThresholdNormalizationTest {

    private record Read(Partitions.Partitioning partitioning, List<Threshold> thresholds) {}

    private static Read read(String source, String behavior) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Ast.Module prepared = compilation.db().ask(new Shapes.Prepared(module)).value();
        Symbols symbols = compilation.db().ask(new Shapes.Scope(module)).value();
        Map<String, Sig> sigs = compilation.db().ask(new Bodies.Signatures(module)).value();
        TypeChecker.Checked checked = compilation.db().ask(new Bodies.Checked(module)).value();
        assertNotNull(checked, "the model under test compiles");

        Ast.SpecBehavior spec = (Ast.SpecBehavior) prepared.behaviors().stream()
                .filter(b -> b.name().equals(behavior)).findFirst().orElseThrow();
        Core body = checked.behaviorBodies().get(behavior);
        assertNotNull(body);
        CoverageSites.Plan plan = CoverageSites.of("m.sou", checked.behaviorBodies());
        List<Threshold> thresholds = GuardThresholds.of(behavior, body, plan,
                spec.params().stream().map(Ast.Param::name).toList(), symbols);
        Partitions.Partitioning base = Partitions.of(spec, sigs.get(behavior), symbols, Exclusions.NONE);
        return new Read(Partitions.withThresholds(base, thresholds, symbols), thresholds);
    }

    private static Axis axis(Partitions.Partitioning partitioning, String path) {
        return partitioning.axes().stream().filter(a -> a.path().toString().equals(path))
                .findFirst().orElseThrow();
    }

    private static List<String> labels(Axis axis) {
        return axis.classes().stream().map(PartitionClass::label).toList();
    }

    private static final String CEILING = """
            module example.trip

            data Amount = Int
                invariant value >= 0

            data Draft = { cost: Amount }
            data Submitted = { cost: Amount }
            data Waiting = { cost: Amount }

            behavior submit : (request: Draft) -> Submitted | Waiting
                constructs Submitted, Waiting

            let submit (request) = {
                guard request.cost.value <= 100000 else Waiting { cost = request.cost }
                Submitted { cost = request.cost }
            }
            """;

    @Test
    void aComparisonDividesAPositionTheTypeLeftWhole() {
        Read read = read(CEILING, "submit");

        assertEquals(1, read.thresholds().size());
        Threshold threshold = read.thresholds().get(0);
        assertEquals("request.cost", threshold.path().toString());
        assertEquals(new BigDecimal(100000), threshold.value());
        assertTrue(threshold.valueBelongsBelow(), "`<= c` puts c on the low side");

        Axis cost = axis(read.partitioning(), "request.cost");
        assertEquals(List.of("0 <= x <= 100000", "100000 < x"), labels(cost));
    }

    /** The newtype's `value` is not a step: the guard and the parameter walk have to spell the same
     * location the same way, or the position becomes two axes and neither is ever covered. */
    @Test
    void aNewtypesValueIsTheSameLocationAsTheNewtype() {
        Read read = read(CEILING, "submit");

        assertEquals(List.of("request.cost"),
                read.thresholds().stream().map(t -> t.path().toString()).toList());
        assertTrue(read.partitioning().axes().stream()
                        .noneMatch(a -> a.path().toString().equals("request.cost.value")),
                "there is no second axis under the newtype's field");
    }

    /** The invariant bounds what exists; the guard says where the behavior changes. The range below
     * zero holds nothing a row could write, so it is not a range to cover. */
    @Test
    void theTypesOwnDomainIsIntersectedIn() {
        Read read = read("""
                module example.bounded

                data Level = Int
                    invariant value >= 0

                data Answer = { n: Int }

                behavior classify : (level: Level) -> Answer
                    constructs Answer

                let classify (level) =
                    if level.value < 10 then Answer { n = 1 } else Answer { n = 2 }
                """, "classify");

        assertEquals(List.of("0 <= x < 10", "10 <= x"), labels(axis(read.partitioning(), "level")));
    }

    @Test
    void severalCutsOnOnePositionBecomeOneRunOfRanges() {
        Read read = read("""
                module example.bands

                data Score = Int

                data Band = { name: String }

                behavior bandFor : (score: Score) -> Band
                    constructs Band

                let bandFor (score) =
                    if score.value < 10 then Band { name = "low" }
                    else if score.value < 20 then Band { name = "mid" }
                    else Band { name = "high" }
                """, "bandFor");

        assertEquals(List.of("x < 10", "10 <= x < 20", "20 <= x"),
                labels(axis(read.partitioning(), "score")));
    }

    /**
     * Short-circuiting is why only a bare comparison is read. An overseas request takes the else arm
     * without `cost` ever being compared, so a row that lands there is not a boundary test of `cost`.
     */
    @Test
    void aCompoundConditionDrawsNoLine() {
        Read read = read("""
                module example.compound

                data Domestic
                data Overseas
                data Kind = Domestic | Overseas

                data Request = { kind: Kind, cost: Int }
                data Answer = { n: Int }

                behavior check : (request: Request) -> Answer
                    constructs Answer

                let check (request) =
                    match request.kind with
                        | Domestic ->
                            if request.cost <= 100 then Answer { n = 1 } else Answer { n = 2 }
                        | Overseas -> Answer { n = 3 }
                """, "check");

        assertEquals(1, read.thresholds().size(), "the bare comparison inside the arm is read");

        Read compound = read("""
                module example.compound2

                data Request = { urgent: Bool, cost: Int }
                data Answer = { n: Int }

                behavior check : (request: Request) -> Answer
                    constructs Answer

                let check (request) =
                    if request.urgent && request.cost <= 100
                        then Answer { n = 1 } else Answer { n = 2 }
                """, "check");

        assertEquals(List.of(), compound.thresholds(),
                "nothing is read out of a condition whose parts may not be evaluated");
    }

    @Test
    void aGuardsBoundaryWantsTheValueAndItsNeighbour() {
        Read read = read(CEILING, "submit");
        Axis cost = axis(read.partitioning(), "request.cost");

        List<BoundaryObligation> obligations = Partitions.obligationsOf(cost, Symbols.none());
        List<String> described = obligations.stream()
                .map(o -> o.side() + " " + Intervals.numberOf(o.value())).toList();

        assertTrue(described.contains("AT 100000"), described.toString());
        assertTrue(described.contains("ABOVE 100001"), described.toString());
        assertTrue(described.contains("AT 0"), "the invariant's own edge is still worth a row");
        assertFalse(described.contains("ABOVE 1"),
                "an invariant's bound has nothing on the far side to reach");
    }

    /**
     * The shipping-fee example from smdd-book chapter 8, and the number it derives: the boundary of
     * "under three thousand" is 2999. Which neighbour is the other class's edge follows from which
     * side of the line the compared value is on, which is why the origin carries it.
     */
    @Test
    void theBoundaryOfAnUnderRuleIsTheValueBelowIt() {
        Read read = read("""
                module example.shipping

                data Yen = Int
                    invariant value >= 0

                data Fee = { yen: Int }

                behavior feeFor : (amount: Yen) -> Fee
                    constructs Fee

                let feeFor (amount) =
                    if amount.value < 3000 then Fee { yen = 500 } else Fee { yen = 0 }
                """, "feeFor");

        Axis amount = axis(read.partitioning(), "amount");
        assertEquals(List.of("0 <= x < 3000", "3000 <= x"), labels(amount));

        List<String> described = Partitions.obligationsOf(amount, Symbols.none()).stream()
                .map(o -> o.side() + " " + Intervals.numberOf(o.value())).toList();
        assertTrue(described.contains("AT 3000"), described.toString());
        assertTrue(described.contains("BELOW 2999"), described.toString());
    }

    /** The same value cut by two rules is one class boundary and two things to exercise. */
    @Test
    void aCutDrawnTwiceKeepsBothRules() {
        Read read = read("""
                module example.twice

                data Level = Int
                    invariant value >= 10

                data Answer = { n: Int }

                behavior classify : (level: Level) -> Answer
                    constructs Answer

                let classify (level) =
                    if level.value < 10 then Answer { n = 1 } else Answer { n = 2 }
                """, "classify");

        Axis level = axis(read.partitioning(), "level");
        Cut at10 = level.cuts().stream()
                .filter(c -> new ObservedValue.Integer(10).equals(c.value())).findFirst()
                .orElseThrow();

        assertEquals(2, at10.origins().size(), "an invariant and a guard both drew it");
        assertTrue(at10.origins().stream().anyMatch(o -> o instanceof OriginRef.InvariantOrigin));
        assertTrue(at10.origins().stream().anyMatch(o -> o instanceof OriginRef.GuardOrigin));
    }
}
