package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Ast;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeChecker;
import souther.compiler.core.Core;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.observe.Classification;
import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.ObservedValue;
import souther.compiler.observe.RowOutcome;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.Output;
import souther.compiler.query.Shapes;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * Why a row could not be placed at a position, and who is entitled to say.
 *
 * <p>A classifier may read through the value it is given: a number at a position is the number
 * inside the newtype named there, because a newtype is not a step in a path. So the value the walk
 * finds and the value a class is about are not always the same node, and only the classifier knows
 * which one it read.
 *
 * <p>Held here because the difference is invisible half the time. A limit reached one wrapper in
 * used to come back as a value that could not be read — right about the row and wrong about what
 * happened to it — while the same failure at the node itself came back correctly, and an unreadable
 * value one wrapper in came back correctly by accident. Which is why nothing noticed.
 */
class WhyAValueCouldNotBePlacedIsTheClassifiersToSayTest {

    private static final String MODEL = """
            module example.trip

            data Domestic
            data Overseas
            data Kind = Domestic | Overseas

            data Amount = Int
                invariant value >= 0

            data Request = { kind: Kind, cost: Amount, plain: Int }
            data Submitted = { cost: Amount }
            data Waiting = { cost: Amount }

            behavior submit : (request: Request) -> Submitted | Waiting
                constructs Submitted, Waiting

            let submit (request) = {
                guard request.cost.value <= 100 else Waiting { cost = request.cost }
                guard request.plain <= 10 else Waiting { cost = request.cost }
                Submitted { cost = request.cost }
            }

            example submit
                | (Request { kind = Domestic, cost = Amount(50), plain = 1 }) -> Submitted
            """;

    private record Read(List<Axis> axes, List<String> parameters, RowOutcome row) {}

    private static Read read() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Ast.Module prepared = compilation.db().ask(new Shapes.Prepared(module)).value();
        Symbols symbols = compilation.db().ask(new Shapes.Scope(module)).value();
        Map<String, Sig> sigs = compilation.db().ask(new Bodies.Signatures(module)).value();
        TypeChecker.Checked checked = compilation.db().ask(new Bodies.Checked(module)).value();
        assertNotNull(checked, "the model under test compiles");
        Ast.SpecBehavior spec = (Ast.SpecBehavior) prepared.behaviors().stream()
                .filter(b -> b.name().equals("submit")).findFirst().orElseThrow();
        Core body = checked.behaviorBodies().get("submit");
        CoverageSites.Plan plan = CoverageSites.of("m.sou", checked.behaviorBodies());
        List<String> parameters = spec.params().stream().map(Ast.Param::name).toList();
        Partitions.Partitioning partitioning = Partitions.withThresholds(
                Partitions.of(spec, sigs.get("submit"), symbols, Exclusions.NONE),
                GuardThresholds.of("submit", body, plan, parameters, symbols).thresholds(), symbols);
        Output.Examples.Of observed = compilation.db()
                .ask(Output.Examples.asked(compilation.db(), module,
                        compilation.sourceIds().get(0))).value();
        assertNotNull(observed);
        return new Read(partitioning.axes(), parameters, observed.rows().get(0));
    }

    /** The row it read, with one of the request's fields replaced. */
    private static RowOutcome giving(Read read, String field, ObservedValue value) {
        ObservedValue.Constructed request = (ObservedValue.Constructed) read.row().inputs().get(0);
        Map<String, ObservedValue> fields = new LinkedHashMap<>(request.fields());
        fields.put(field, value);
        return new RowOutcome(read.row().at(), read.row().target(), read.row().description(),
                read.row().stage(), read.row().disposition(), read.row().failurePhase(),
                read.row().expectedArm(), read.row().resultArm(), read.row().inputCases(),
                List.of(new ObservedValue.Constructed(request.type(), fields)), read.row().hits(),
                read.row().stepsSpent());
    }

    /** The newtype the row wrote at {@code cost}, holding {@code inner} where its number was. */
    private static ObservedValue wrapping(Read read, ObservedValue inner) {
        ObservedValue.Constructed request = (ObservedValue.Constructed) read.row().inputs().get(0);
        ObservedValue.Constructed amount = (ObservedValue.Constructed) request.field("cost");
        Map<String, ObservedValue> value = new LinkedHashMap<>(amount.fields());
        value.put("value", inner);
        return new ObservedValue.Constructed(amount.type(), value);
    }

    private static Classification at(Read read, RowOutcome row, String path) {
        Map<AxisId, Classification> classes = RowClasses.of(row, read.parameters(), read.axes());
        return classes.entrySet().stream().filter(e -> e.getKey().path().equals(path))
                .map(Map.Entry::getValue).findFirst()
                .orElseThrow(() -> new AssertionError("no axis at " + path));
    }

    private static Incompleteness.Code why(Classification where) {
        return assertInstanceOf(Classification.Unclassified.class, where).reason().code();
    }

    @Test
    void aValueTheLimitStoppedSaysSoWhereItIsTheValueItself() {
        Read read = read();

        assertEquals(Incompleteness.Code.VALUE_TRUNCATED,
                why(at(read, giving(read, "plain", new ObservedValue.Truncated()), "request.plain")));
    }

    @Test
    void aValueTheWalkCouldNotReadSaysSoWhereItIsTheValueItself() {
        Read read = read();

        assertEquals(Incompleteness.Code.VALUE_UNREADABLE,
                why(at(read, giving(read, "plain", new ObservedValue.Unknown("gone")),
                        "request.plain")));
    }

    /** The one this issue is about. A newtype is not a step, so the limit was reached at a node the
     * walk never names — and the class that reads through it is the only thing that knows. */
    @Test
    void aValueTheLimitStoppedInsideANewtypeSaysSoTo() {
        Read read = read();

        assertEquals(Incompleteness.Code.VALUE_TRUNCATED,
                why(at(read, giving(read, "cost", wrapping(read, new ObservedValue.Truncated())),
                        "request.cost")));
    }

    @Test
    void aValueTheWalkCouldNotReadInsideANewtypeSaysSoTo() {
        Read read = read();

        assertEquals(Incompleteness.Code.VALUE_UNREADABLE,
                why(at(read, giving(read, "cost", wrapping(read, new ObservedValue.Unknown("gone"))),
                        "request.cost")));
    }

    /** And a value every class could read still lands where it did. */
    @Test
    void aReadableValueIsStillPlacedInTheClassThatHoldsIt() {
        Read read = read();

        assertEquals(new Classification.Classified("request.cost/0 <= x <= 100"),
                at(read, read.row(), "request.cost"));
        assertEquals(new Classification.Classified("request.plain/x <= 10"),
                at(read, read.row(), "request.plain"));
        assertEquals(new Classification.Classified("Domestic"),
                at(read, read.row(), "request.kind"));
    }

    // --- what the contract says cannot happen ---------------------------------------------------

    /** The same axis, with classes that answer however this asks them to. */
    private static List<Axis> answering(Read read, String path, Classifier... classifiers) {
        Axis real = read.axes().stream().filter(a -> a.path().toString().equals(path))
                .findFirst().orElseThrow();
        List<PartitionClass> classes = new java.util.ArrayList<>();
        for (int i = 0; i < classifiers.length; i++) {
            classes.add(PartitionClass.of("c" + i, "c" + i, classifiers[i],
                    RepresentativeSource.none()));
        }
        return List.of(new Axis(real.id(), real.path(), real.type(), classes, real.cuts()));
    }

    /**
     * A readable value in none of the classes is the partition's contract broken.
     *
     * <p>{@code Axis} says its classes are exclusive and exhaustive over the position's values, so a
     * value every class read and none holds is not a third thing a row can be. Reporting it as a row
     * that could not be read would answer a defect in the partition with a measurement failure, and
     * the report would name the row.
     */
    @Test
    void everyClassReadingTheValueAndNoneHoldingItIsNotAnAnswer() {
        Read read = read();
        List<Axis> axes = answering(read, "request.plain",
                _ -> Membership.NO_MATCH, _ -> Membership.NO_MATCH);

        IllegalStateException thrown = assertThrows(IllegalStateException.class,
                () -> RowClasses.of(read.row(), read.parameters(), axes));
        org.junit.jupiter.api.Assertions.assertTrue(
                thrown.getMessage().contains("holds a value it read"), thrown.getMessage());
    }

    /**
     * And two classes disagreeing about why they could not read it is the same kind of thing.
     *
     * <p>One value, two readings of whether it is there. Picking between them would be inventing a
     * precedence for a question nothing has asked: today every class of a numeric position reads
     * through the same reader and they cannot disagree.
     */
    @Test
    void twoClassesDisagreeingAboutWhyIsNotAnAnswerEither() {
        Read read = read();
        List<Axis> axes = answering(read, "request.plain",
                _ -> new Membership.Incomplete(Incompleteness.Code.VALUE_TRUNCATED),
                _ -> new Membership.Incomplete(Incompleteness.Code.VALUE_UNREADABLE));

        IllegalStateException thrown = assertThrows(IllegalStateException.class,
                () -> RowClasses.of(read.row(), read.parameters(), axes));
        org.junit.jupiter.api.Assertions.assertTrue(
                thrown.getMessage().contains("disagree about why"), thrown.getMessage());
    }
}
