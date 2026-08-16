package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.check.Prepared;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.Shapes;

import java.util.List;
import java.util.Map;

import souther.compiler.values.AdmissibleSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * The classes of a position are the values it can hold, and evidence only ever tells them apart
 * more finely.
 *
 * <p>Two rules, and they are the same rule read in the two directions the classes can move in.
 *
 * <p>What a type declares and what a position can hold are separate facts, crossed where the
 * position is read: {@code data StageI = Stage invariant value == Qualified} declares three cases
 * and holds one, and the other two are rows nobody can write (E1903). That crossing was made
 * against the intervals alone, so the same rule written as an ordering took the cases away and the
 * same rule written as an equality did not — which is a partition that turns on how a rule is
 * spelled rather than on what it says.
 *
 * <p>And evidence arriving later refines: a body comparing a position it already has classes for
 * draws a line among them rather than replacing them. Replacement is how a class the model states
 * would come to be lost to a rule the body writes, and the loss reads as the model never having
 * stated it.
 */
class AClassIsOneThePositionCanHoldAndNothingTakesItAwayTest {

    private record Read(Compilation compilation, String module, Hir.SpecBehavior spec, Sig sig,
                        Symbols symbols) {}

    private static Read of(String source, String behavior) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Prepared prepared = compilation.db().ask(new Shapes.Prepared(module)).value();
        Map<String, Sig> sigs = compilation.db().ask(new Bodies.Signatures(module)).value();
        Symbols symbols = compilation.db().ask(new Shapes.Scope(module)).value();
        Hir.SpecBehavior spec = (Hir.SpecBehavior) prepared.behaviors().stream()
                .filter(b -> b.name().equals(behavior)).findFirst().orElseThrow();
        return new Read(compilation, module, spec, sigs.get(behavior), symbols);
    }

    /** The classes of the one position, off the declarations alone. */
    private static List<String> declared(String source, String behavior) {
        Read read = of(source, behavior);
        return classesOf(Partitions.of(read.spec(), read.sig(), read.symbols(), Exclusions.NONE));
    }

    /** And the same with what the behavior's own body draws taken in. */
    private static List<String> withBody(String source, String behavior) {
        Read read = of(source, behavior);
        Bodies.Elaborated checked =
                read.compilation().db().ask(new Bodies.Checked(read.module())).value();
        assertNotNull(checked, "the model under test compiles");
        Core body = checked.behaviorBodies().get(behavior);
        assertNotNull(body, "the behavior under test has a body");
        GuardThresholds.Guards guards = GuardThresholds.of(behavior, body,
                CoverageSites.of(checked.behaviorBodies()),
                read.spec().params().stream().map(Hir.Param::name).toList(), read.symbols());
        Partitions.Partitioning base =
                Partitions.of(read.spec(), read.sig(), read.symbols(), Exclusions.NONE);
        return classesOf(Partitions.withThresholds(base, guards.thresholds(), read.symbols(),
                guards.unread(), guards.singled(), guards.between()));
    }

    /** The one axis, whichever phase produced it. */
    private static Axis only(Partitions.Partitioning partitioning) {
        assertEquals(1, partitioning.axes().size(), partitioning.axes().toString());
        return partitioning.axes().get(0);
    }

    private static List<String> classesOf(Partitions.Partitioning partitioning) {
        assertEquals(1, partitioning.axes().size(), partitioning.axes().toString());
        return classesAt(partitioning, partitioning.axes().get(0).path().toString());
    }

    /** The classes of the position at {@code path}, where a behavior has more than one. */
    private static List<String> classesAt(Partitions.Partitioning partitioning, String path) {
        return partitioning.axes().stream()
                .filter(each -> each.path().toString().equals(path))
                .findFirst()
                .orElseThrow(() -> new AssertionError("no axis at " + path + " in "
                        + partitioning.axes()))
                .classes().stream().map(PartitionClass::id).toList();
    }

    /** The classes at {@code path}, off the declarations alone. */
    private static List<String> declaredAt(String source, String behavior, String path) {
        Read read = of(source, behavior);
        return classesAt(Partitions.of(read.spec(), read.sig(), read.symbols(), Exclusions.NONE),
                path);
    }

    /**
     * A case the position cannot hold is not one of its classes, whichever way the rule is written.
     *
     * <p>{@code >= Qualified} already took the case away, through the intervals. The equality says
     * the same thing about the same position and left all three, so a row was asked for at two
     * values the constructor refuses.
     */
    @Test
    void anEqualityOverCasesTakesTheOnesItRefusesAway() {
        String model = """
                module g

                data Prospecting
                data Qualified
                data Won
                data Stage = Prospecting | Qualified | Won

                data StageI = Stage
                    invariant value == Qualified

                data Accepted = { at: String }

                behavior classify : (s: StageI) -> Accepted
                """;

        assertEquals(List.of("Qualified"), declared(model, "classify"));
    }

    /** And the same of a boolean, which has two values and a rule can leave one. */
    @Test
    void anEqualityOverABooleanLeavesTheValueItNames() {
        assertEquals(List.of("true"), declared("""
                module g

                data Yes = Bool
                    invariant value == true

                data Accepted = { at: String }

                behavior classify : (y: Yes) -> Accepted
                """, "classify"));
    }

    /**
     * And the classes stay in the order the type declares them, not the order the rule names them.
     *
     * <p>The classes are the position's, and a reader lists them as the model wrote them. Ordered
     * by the rule, one partition would be written two ways depending on which value the author put
     * first — in the report, and in the rows a generator offers from it.
     */
    @Test
    void theClassesLeftAreInTheOrderTheTypeDeclaresThem() {
        assertEquals(List.of("Prospecting", "Won"), declared("""
                module g

                data Prospecting
                data Qualified
                data Won
                data Stage = Prospecting | Qualified | Won

                data StageI = Stage
                    invariant either = value == Won || value == Prospecting

                data Accepted = { at: String }

                behavior classify : (s: StageI) -> Accepted
                """, "classify"));
    }

    /**
     * A position that can hold none of its classes keeps them, rather than coming back divided no
     * way.
     *
     * <p>Nothing left is not an empty partition: it is a value nothing can build, which is refused
     * where the declaration is (E1013) and is why this model does not compile. What is asserted is
     * that the reading of it does not answer with the one sentence this whole protocol is against —
     * a position the model divides three ways, reported as one it divides no way, because the rules
     * then refuse all three.
     */
    @Test
    void aPositionThatCanHoldNoneOfItsClassesIsNotOneDividedNoWay() {
        assertEquals(List.of("Prospecting", "Qualified", "Won"), declared("""
                module g

                data Prospecting
                data Qualified
                data Won
                data Stage = Prospecting | Qualified | Won

                data StageI = Stage
                    invariant both = value == Qualified && value == Won

                data Accepted = { at: String }

                behavior classify : (s: StageI) -> Accepted
                """, "classify"));
    }

    /**
     * A case a rule refuses is not a class of the position, said as a denial as well as as a naming.
     *
     * <p>The other half of the same crossing, and the half a mixed sum reaches. Where every value
     * of a type can be written out — a boolean, a sum of unit cases — a denial is turned into the
     * values it leaves where it is read, and the crossing sees a finite set. Where they cannot, it
     * stays a denial: {@code State} has a case holding a record, so {@code /= Missing} is every
     * value but one and names none of the ones left.
     *
     * <p>A class is dropped where the rules leave it nothing, which is one rule and two proofs. A
     * finite set proves it by holding no value of the class; a denial proves it by excluding every
     * value the class holds, which is provable of a class that is one value and not of one that is
     * a record.
     */
    @Test
    void aCaseADenialRefusesIsNotAClassEither() {
        assertEquals(List.of("Present"), declared("""
                module g

                data Missing
                data Present = { note: String }
                data State = Missing | Present

                data AvailableState = State
                    invariant here = value /= Missing

                data Accepted = { at: String }

                behavior classify : (s: AvailableState) -> Accepted
                """, "classify"));
    }

    /** And a denial over a boolean leaves the other value, which is the same rule where the values
     *  can be written out. */
    @Test
    void aDenialOverABooleanLeavesTheOtherValue() {
        assertEquals(List.of("false"), declared("""
                module g

                data No = Bool
                    invariant here = value /= true

                data Accepted = { at: String }

                behavior classify : (n: No) -> Accepted
                """, "classify"));
    }

    /**
     * A denial of one value of a class that holds many takes the class away from nothing.
     *
     * <p>What the proof is for. A record case holds every value its fields can be given, so a rule
     * refusing one of them refuses none of the class — and a crossing that dropped it on a match
     * would take away a class the model states and the position can reach.
     */
    @Test
    void aDenialOfOneValueDoesNotTakeAwayAClassThatHoldsMany() {
        assertEquals(List.of("Missing", "Present"), declaredAt("""
                module g

                data Missing
                data Present = { note: String }
                data State = Missing | Present

                data Held = { state: State, note: String }
                    invariant here = note /= "x"

                data Accepted = { at: String }

                behavior classify : (h: Held) -> Accepted
                """, "classify", "h.state"));
    }

    /** A case the rule leaves is still a class, so the crossing takes away only what it must. */
    @Test
    void aRuleThatRefusesNothingLeavesEveryCase() {
        assertEquals(List.of("Prospecting", "Qualified", "Won"), declared("""
                module g

                data Prospecting
                data Qualified
                data Won
                data Stage = Prospecting | Qualified | Won

                data StageI = Stage

                data Accepted = { at: String }

                behavior classify : (s: StageI) -> Accepted
                """, "classify"));
    }

    /**
     * How much of the rules the classes were derived under survives every phase.
     *
     * <p>Nothing reads it yet, which is the whole reason to hold it here: a phase that dropped it
     * would leave every measure saying what it says today, and the loss would show up the day
     * somebody asks whether a class is one a value can be built for. The classes are the values the
     * model singled out either way; what the answer beside them says is that a rule went unread and
     * may yet refuse one of them.
     */
    @Test
    void howMuchWasReadSurvivesTheBodyAsWellAsTheDeclarations() {
        String model = """
                module g

                data Code = String
                    invariant enumerated = value == "a" || value == "b"
                    invariant shape = String.matches("[a-z]", value)

                data Accepted = { at: String }
                data Refused = { at: String }

                behavior classify : (c: Code) -> Accepted | Refused
                    constructs Accepted, Refused

                let classify (c) =
                    if String.length(c.value) == 1 then Accepted { at = "x" }
                    else Refused { at = "y" }
                """;
        Read read = of(model, "classify");
        Partitions.Partitioning base =
                Partitions.of(read.spec(), read.sig(), read.symbols(), Exclusions.NONE);

        assertInstanceOf(AdmissibleSet.Completeness.Partial.class, only(base).read(),
                "a rule about this position went unread, and the classes were made anyway");
        assertEquals(only(base).read(), only(withThresholdsOf(read, base)).read(),
                "what a body draws does not change what was read about the position's values");
    }

    /** The same partitioning, with what the behavior's body draws taken in. */
    private static Partitions.Partitioning withThresholdsOf(Read read,
                                                            Partitions.Partitioning base) {
        Bodies.Elaborated checked =
                read.compilation().db().ask(new Bodies.Checked(read.module())).value();
        assertNotNull(checked, "the model under test compiles");
        Core body = checked.behaviorBodies().get(read.spec().name());
        assertNotNull(body, "the behavior under test has a body");
        GuardThresholds.Guards guards = GuardThresholds.of(read.spec().name(), body,
                CoverageSites.of(checked.behaviorBodies()),
                read.spec().params().stream().map(Hir.Param::name).toList(), read.symbols());
        return Partitions.withThresholds(base, guards.thresholds(), read.symbols(),
                guards.unread(), guards.singled(), guards.between());
    }

    /**
     * A line a body draws on a position that already has classes leaves them where they are.
     *
     * <p>The classes the model states are finer than the ranges either side of a line — every value
     * of the position is one of them — so ranges rebuilt from the line would take away distinctions
     * the model already made. The line is still a line and still owes its rows.
     */
    @Test
    void anOrderingInABodyDoesNotReplaceTheClassesTheModelStates() {
        String model = """
                module g

                data Small = Int
                    invariant value == 1 || value == 2

                data Accepted = { at: String }
                data Refused = { at: String }

                behavior classify : (n: Small) -> Accepted | Refused
                    constructs Accepted, Refused

                let classify (n) =
                    if n.value >= 2 then Accepted { at = "x" } else Refused { at = "y" }
                """;

        assertEquals(List.of("1", "2"), declared(model, "classify"));
        assertEquals(List.of("1", "2"), withBody(model, "classify"));
    }

    /** And neither does a body singling a value out: the value already has a class of its own, and
     *  the rest of the position is the other classes rather than one lump of everything else. */
    @Test
    void singlingAValueOutInABodyDoesNotReplaceThemEither() {
        String model = """
                module g

                data Small = Int
                    invariant value == 1 || value == 2

                data Accepted = { at: String }
                data Refused = { at: String }

                behavior classify : (n: Small) -> Accepted | Refused
                    constructs Accepted, Refused

                let classify (n) =
                    if n.value == 1 then Accepted { at = "x" } else Refused { at = "y" }
                """;

        assertEquals(List.of("1", "2"), withBody(model, "classify"));
    }
}
