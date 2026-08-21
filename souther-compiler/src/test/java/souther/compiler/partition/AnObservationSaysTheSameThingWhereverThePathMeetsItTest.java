package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Scopes;
import souther.compiler.ast.Hir;
import souther.compiler.check.Prepared;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeChecker;
import souther.compiler.core.Core;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.TermPath;
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

/**
 * What a walk to a position inside a record says about not getting there.
 *
 * <p>An observation that did not arrive is already the reason it did not: {@link ObservedValue}
 * carries a case for a limit that stopped it and a case for a value it could not read, and both
 * stand where the value would have been. So the walk is not asked to work anything out. It is asked
 * not to throw away what it ran into.
 *
 * <p>Which it did, in one place only. A record the node budget did not reach stands at the position
 * itself and comes back as a limit that stopped it, and stands one field short of the position and
 * comes back as a value nobody could read. One value, two answers, told apart by nothing but how
 * many fields were left to walk.
 */
class AnObservationSaysTheSameThingWhereverThePathMeetsItTest {

    private static final String MODEL = """
            module example.booking

            data Amount = Int
                invariant value >= 0

            data Interval = { startsAt: Int, endsAt: Int }

            data Request = { cost: Amount, interval: Interval }
            data Booked = { cost: Amount }
            data Waiting = { cost: Amount }

            behavior book : (request: Request) -> Booked | Waiting
                constructs Booked, Waiting

            let book (request) = {
                guard request.interval.startsAt <= 10 else Waiting { cost = request.cost }
                Booked { cost = request.cost }
            }

            example book
                | (Request { cost = Amount(50),
                             interval = Interval { startsAt = 1, endsAt = 2 } }) -> Booked
            """;

    private static final String POSITION = "request.interval.startsAt";

    private record Read(List<Axis> axes, BehaviorInputs inputs, RowOutcome row) {}

    private static Read read() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Prepared prepared = compilation.db().ask(new Shapes.Prepared(module)).value();
        Symbols symbols = Scopes.derived(compilation.db(), module).value();
        Map<String, Sig> sigs = compilation.db().ask(new Bodies.Signatures(module)).value();
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        assertNotNull(checked, "the model under test compiles");
        Hir.SpecBehavior spec = (Hir.SpecBehavior) prepared.behaviors().stream()
                .filter(b -> b.name().equals("book")).findFirst().orElseThrow();
        Core body = checked.behaviorBodies().get("book");
        CoverageSites.Plan plan = CoverageSites.of(checked.behaviorBodies());
        List<String> parameters = spec.params().stream().map(Hir.Param::name).toList();
        Partitions.Partitioning partitioning = Partitions.withThresholds(
                Partitions.of(spec.name(), InputDomain.of(spec, sigs.get("book"), symbols, souther.compiler.query.ReadAs.THE_COMPILATION_DOES), symbols, souther.compiler.query.ReadAs.THE_COMPILATION_DOES),
                GuardThresholds.of("book", body, plan,
                compilation.db().ask(new souther.compiler.query.Adequacy.Inputs(module)).value().get("book"), symbols).thresholds(), symbols, souther.compiler.query.ReadAs.THE_COMPILATION_DOES);
        Output.Examples.Of observed = compilation.db()
                .ask(Output.Examples.asked(compilation.db(), module,
                        compilation.sourceIds().get(0))).value();
        assertNotNull(observed);
        return new Read(partitioning.axes(),
                new BehaviorInputs(parameters, sigs.get("book").inputTypes(), symbols, souther.compiler.query.ReadAs.THE_COMPILATION_DOES),
                observed.rows().get(0));
    }

    /** The row it read, with the request's {@code interval} replaced by whatever stands there. */
    private static RowOutcome givingInterval(Read read, ObservedValue value) {
        ObservedValue.Constructed request = (ObservedValue.Constructed) read.row().inputs().get(0);
        Map<String, ObservedValue> fields = new LinkedHashMap<>(request.fields());
        fields.put("interval", value);
        return new RowOutcome(read.row().at(), read.row().target(), read.row().identity(),
                read.row().stage(), read.row().disposition(), read.row().failurePhase(),
                read.row().expectedArm(), read.row().resultArm(), read.row().inputCases(),
                List.of(new ObservedValue.Constructed(request.type(), fields)), read.row().run());
    }

    /** The interval the row wrote, with {@code inner} where the position's number was. */
    private static ObservedValue intervalHolding(Read read, ObservedValue inner) {
        ObservedValue.Constructed interval = (ObservedValue.Constructed)
                ((ObservedValue.Constructed) read.row().inputs().get(0)).field("interval");
        Map<String, ObservedValue> fields = new LinkedHashMap<>(interval.fields());
        fields.put("startsAt", inner);
        return new ObservedValue.Constructed(interval.type(), fields);
    }

    private static Incompleteness.Code why(Read read, RowOutcome row) {
        Map<AxisId, Classification> classes = RowClasses.of(row, read.inputs(), read.axes());
        Classification where = classes.entrySet().stream()
                .filter(e -> e.getKey().term().equals(POSITION))
                .map(Map.Entry::getValue).findFirst()
                .orElseThrow(() -> new AssertionError("no axis at " + POSITION));
        return assertInstanceOf(Classification.Unclassified.class, where).reason().code();
    }

    private static TermPath position(Read read) {
        return read.axes().stream().filter(a -> a.path().toString().equals(POSITION))
                .findFirst().orElseThrow().path();
    }

    /**
     * A limit that stopped the observation says so from either place on the path.
     *
     * <p>Both, in one test, because neither is the claim on its own. The position itself was already
     * right and the field above it was already wrong, and what was wrong is that they differed.
     */
    @Test
    void aLimitThatStoppedTheObservationSaysSoFromAnywhereOnThePath() {
        Read read = read();

        assertEquals(Incompleteness.Code.VALUE_TRUNCATED,
                why(read, givingInterval(read, intervalHolding(read, new ObservedValue.Truncated()))),
                "the limit was reached at the position");
        assertEquals(Incompleteness.Code.VALUE_TRUNCATED,
                why(read, givingInterval(read, new ObservedValue.Truncated())),
                "the limit was reached one field above the position");
    }

    /** And so does a value the observer could not read, which was right in both places by accident:
     * the answer the walk invented for everything happened to be this one. */
    @Test
    void aValueTheObserverCouldNotReadSaysSoFromAnywhereOnThePath() {
        Read read = read();

        assertEquals(Incompleteness.Code.VALUE_UNREADABLE,
                why(read, givingInterval(read,
                        intervalHolding(read, new ObservedValue.Unknown("gone")))));
        assertEquals(Incompleteness.Code.VALUE_UNREADABLE,
                why(read, givingInterval(read, new ObservedValue.Unknown("gone"))));
    }

    /**
     * A record that was observed and does not hold the field the path names is the other thing, and
     * stays the other thing.
     *
     * <p>Nothing was stopped here: the walk arrived, read what was there, and the path asked for a
     * field of it that the observation does not have. There is no reason to keep because the
     * observation has none to give, which is what is left for the walk to answer on its own.
     */
    @Test
    void aFieldTheObservationDoesNotHoldIsStillTheWalksOwnAnswer() {
        Read read = read();
        ObservedValue.Constructed interval = (ObservedValue.Constructed)
                ((ObservedValue.Constructed) read.row().inputs().get(0)).field("interval");

        assertEquals(Incompleteness.Code.VALUE_UNREADABLE,
                why(read, givingInterval(read,
                        new ObservedValue.Constructed(interval.type(), Map.of()))));
    }

    /**
     * What the boundary's caller sees, which is why this changes nothing for it.
     *
     * <p>{@code valueAt} already hands back a stopped observation where the path ends on one — the
     * loop runs out of fields and returns what it is holding — so a caller that asks it for a number
     * already meets one and reads it as no number. Keeping the same value from one field earlier
     * gives that caller a value it already handles rather than a new one.
     */
    @Test
    void theValueAtAPositionIsTheStoppedObservationItself() {
        Read read = read();

        assertInstanceOf(ObservedValue.Truncated.class,
                read.inputs().valueAt(givingInterval(read, intervalHolding(read,
                        new ObservedValue.Truncated())), position(read)),
                "the limit was reached at the position");
        assertInstanceOf(ObservedValue.Truncated.class,
                read.inputs().valueAt(givingInterval(read, new ObservedValue.Truncated()), position(read)),
                "the limit was reached one field above the position");
    }
}
