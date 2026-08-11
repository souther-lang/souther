package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceNameResolver;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BoundaryAssessment;
import souther.compiler.check.NumericMeasures;
import souther.compiler.query.Compilation;
import souther.compiler.types.ValueName;
import souther.compiler.report.AdequacyReport;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Which coordinates a clause reaches decides whether it places an edge, and the declaration holding
 * the clause does not (spec §a-clause-places-an-edge-where-it-reaches-one-coordinate).
 *
 * <p>A bound was read off the newtype chain of the position's own type and off nothing else, so the
 * same rule was measured or unmeasured according to where the author happened to write it.
 * {@code data Cart = List<Int> invariant List.length(value) >= 1} drew a line at 1 and
 * {@code data Cart = { lines: List<OrderLine> } invariant List.length(lines) >= 1} drew none — and an
 * aggregate with a second field has no choice but the second spelling. The measure rewarded wrapping
 * every constrained field in a newtype of its own, which is a modelling choice and says nothing about
 * the rule being stated (#649).
 *
 * <p>What the older rule protected is the relational case, and that is what the negative half here is
 * for. A clause relating two coordinates still divides neither and still places nothing: taking a
 * range in is not the same act as putting an edge in it, and a position whose only limit is another
 * position's is one the model draws no line through.
 */
class AClauseReachingOneCoordinatePlacesAnEdgeTest {

    /**
     * The three shapes of #649 and the shapes that must stay lineless, in one module.
     *
     * <p>Together on purpose: what the measure says about any one of these is only right if it is
     * still right beside the others, and the reading that produced them is one reading. Every row is
     * written away from the line so that a line which exists shows up as a gap naming its value.
     */
    private static final String MODEL = """
            module demo

            data Tally = { n: Int } invariant n >= 1
            data Bag   = { xs: List<Int> } invariant List.length(xs) >= 1
            data Both  = { n: Int } invariant n >= 1 invariant n <= 10

            data Span  = { startsAt: Int, endsAt: Int } invariant startsAt < endsAt
            data Floor = { n: Int, min: Int } invariant n >= min
            data R     = { a: Int, b: Int } invariant a < b invariant b <= 10

            data B     = Int invariant value <= 10
            data Under = { a: Int, b: B } invariant a < b.value

            data Inner = { n: Int } invariant n >= 1
            data Outer = { inner: Inner }
            data Tight = { inner: Inner } invariant inner.n >= 5

            data Ok = { size: Int }

            behavior onTally : (v: Tally) -> Ok
                constructs Ok
            let onTally (v) = Ok { size = v.n }

            behavior onBag : (v: Bag) -> Ok
                constructs Ok
            let onBag (v) = Ok { size = List.length(v.xs) }

            behavior onBoth : (v: Both) -> Ok
                constructs Ok
            let onBoth (v) = Ok { size = v.n }

            behavior onSpan : (v: Span) -> Ok
                constructs Ok
            let onSpan (v) = Ok { size = v.startsAt }

            behavior onFloor : (v: Floor) -> Ok
                constructs Ok
            let onFloor (v) = Ok { size = v.n }

            behavior onR : (v: R) -> Ok
                constructs Ok
            let onR (v) = Ok { size = v.a }

            behavior onUnder : (v: Under) -> Ok
                constructs Ok
            let onUnder (v) = Ok { size = v.a }

            behavior onOuter : (v: Outer) -> Ok
                constructs Ok
            let onOuter (v) = Ok { size = v.inner.n }

            behavior onTight : (v: Tight) -> Ok
                constructs Ok
            let onTight (v) = Ok { size = v.inner.n }

            example onTally | (Tally { n = 4 }) -> Ok { size = 4 }
            example onBag   | (Bag { xs = [1, 2, 3] }) -> Ok { size = 3 }
            example onBoth  | (Both { n = 4 }) -> Ok { size = 4 }
            example onSpan  | (Span { startsAt = 3, endsAt = 4 }) -> Ok { size = 3 }
            example onFloor | (Floor { n = 4, min = 2 }) -> Ok { size = 4 }
            example onR     | (R { a = 3, b = 4 }) -> Ok { size = 3 }
            example onUnder | (Under { a = 3, b = B(4) }) -> Ok { size = 3 }
            example onOuter | (Outer { inner = Inner { n = 4 } }) -> Ok { size = 4 }
            example onTight | (Tight { inner = Inner { n = 9 } }) -> Ok { size = 9 }
            """;

    /** The same rules written on newtypes, which were measured all along. Held beside the rest so
     *  that the shapes below are read as the same rule reaching the same place, and so that a repair
     *  taking these away would be caught by the test that added the others. */
    private static final String ON_NEWTYPES = """
            module newtypes

            data Name  = String    invariant String.length(value) >= 1
            data Cart  = List<Int> invariant List.length(value) >= 1
            data Count = Int       invariant value >= 1
            data Hop   = { n: Count }
            data Moved = { n: Count } invariant n.value >= 5

            data Ok = { size: Int }

            behavior onName : (v: Name) -> Ok
                constructs Ok
            let onName (v) = Ok { size = String.length(v.value) }

            behavior onCart : (c: Cart) -> Ok
                constructs Ok
            let onCart (c) = Ok { size = List.length(c.value) }

            behavior onHop : (v: Hop) -> Ok
                constructs Ok
            let onHop (v) = Ok { size = v.n.value }

            behavior onMoved : (v: Moved) -> Ok
                constructs Ok
            let onMoved (v) = Ok { size = v.n.value }

            example onName  | (Name("abc"))            -> Ok { size = 3 }
            example onCart  | (Cart([1, 2, 3]))        -> Ok { size = 3 }
            example onHop   | (Hop { n = Count(9) })   -> Ok { size = 9 }
            example onMoved | (Moved { n = Count(9) }) -> Ok { size = 9 }
            """;

    /** A record stating a bound on a number of its own places the edge a newtype over that number
     *  would have placed, and names itself. */
    @Test
    void aRecordsBoundOnItsOwnNumberPlacesAnEdge() {
        String report = report(MODEL);

        assertTrue(report.contains("no row is at onTally/v.n = 1 (invariant Tally (min))"), report);
    }

    /**
     * And a bound on how much one of its fields holds.
     *
     * <p>The coordinate is the length and not the list, so the line is named by the length: the rule
     * counts the field rather than saying what the field is.
     */
    @Test
    void aRecordsBoundOnALengthOfItsOwnPlacesAnEdge() {
        String report = report(MODEL);

        assertTrue(report.contains(
                "no row is at onBag/List.length(v.xs) = 1 (invariant Bag (min))"), report);
    }

    /** Both ends, so that this is read as the rules being met and not as a floor being special. */
    @Test
    void bothEndsOfARecordsOwnBoundAreEdges() {
        String report = report(MODEL);

        assertTrue(report.contains("no row is at onBoth/v.n = 1 (invariant Both (min))"), report);
        assertTrue(report.contains("no row is at onBoth/v.n = 10 (invariant Both (max))"), report);
    }

    /** A clause governing the position from the declaration it sits inside reaches it, and names
     *  that declaration rather than the value it was reached through. */
    @Test
    void aClauseOnTheRecordAPositionSitsInsideReachesIt() {
        String report = report(MODEL);

        assertTrue(report.contains(
                "no row is at onOuter/v.inner.n = 1 (invariant Inner (min))"), report);
    }

    /** And the outer record's own clause where it is the tighter of the two. */
    @Test
    void anOuterClauseThatIsTighterOwnsTheLine() {
        String report = report(MODEL);

        assertTrue(report.contains(
                "no row is at onTight/v.inner.n = 5 (invariant Tight (min))"), report);
    }

    /**
     * The rules written on names wrapped round a record, at a parameter and inside one.
     *
     * <p>Its own module, and with no rows: what is asked is which lines the model draws, and a row
     * would only say whether one was met.
     *
     * <p>`Held` is the case a wrapper reached only at the top would miss. Nothing is written on
     * `Held` or on `Base`; the rule is `Wrapped`'s, and the position is two steps down from the
     * parameter.
     */
    private static final String WRAPPERS = """
            module wrappers

            data Base        = { n: Int }
            data Wrapped     = Base invariant value.n >= 1
            data Held        = { w: Wrapped }

            data Bag         = { xs: List<Int> }
            data NonEmptyBag = Bag invariant List.length(value.xs) >= 1
            data HeldBag     = { b: NonEmptyBag }

            data W1          = Base
            data W2          = W1 invariant value.value.n >= 2
            data Stacked     = { w: W2 }

            data Ok = { size: Int }

            behavior onWrapped : (v: Wrapped) -> Ok
                constructs Ok
            let onWrapped (v) = Ok { size = v.n }

            behavior onNonEmpty : (v: NonEmptyBag) -> Ok
                constructs Ok
            let onNonEmpty (v) = Ok { size = List.length(v.xs) }

            behavior onHeld : (v: Held) -> Ok
                constructs Ok
            let onHeld (v) = Ok { size = v.w.n }

            behavior onHeldBag : (v: HeldBag) -> Ok
                constructs Ok
            let onHeldBag (v) = Ok { size = List.length(v.b.xs) }

            behavior onStacked : (v: Stacked) -> Ok
                constructs Ok
            let onStacked (v) = Ok { size = v.w.n }
            """;

    /**
     * A wrapper's rule reaches a position inside a record as well as at a parameter.
     *
     * <p>The place a wrapper read once, at the root of the walk, does not reach. `Held` holds a
     * `Wrapped` and states nothing itself, so the line at its `w.n` is `Wrapped`'s and arrives from a
     * name worn part way down. A wrapper met on the way is the general case and a wrapper at the top
     * is one instance of it, so reading only the second leaves the rule true of parameters and false
     * of fields.
     */
    @Test
    void aWrappersRuleReachesAPositionInsideARecord() {
        Map<String, BoundaryAssessment> lines = linesOf(WRAPPERS, "wrappers");

        assertEquals("invariant Wrapped (min)", lines.get("onHeld/v.w.n = 1").origin());
        assertEquals("invariant NonEmptyBag (min)",
                lines.get("onHeldBag/List.length(v.b.xs) = 1").origin());
    }

    /** And through as many names as are worn, since a name wrapped round a value is not a step. */
    @Test
    void aWrappersRuleReachesThroughAStackOfNames() {
        Map<String, BoundaryAssessment> lines = linesOf(WRAPPERS, "wrappers");

        assertEquals("invariant W2 (min)", lines.get("onStacked/v.w.n = 2").origin());
    }

    /**
     * A name wrapped round a record reaches the record's positions.
     *
     * <p>The place left over when the record and the declarations under it were read. A wrapper is
     * another place the same rule can be written, so reading the record and not the names round it
     * puts this issue back one level up — and the walk cannot miss the shape, since the positions it
     * takes apart are the record's either way.
     *
     * <p>The line is the wrapper's, and the {@code value} the clause is written through is not in
     * it: a newtype's value is the same location as the newtype, so the clause names the {@code n} a
     * reader of a `Wrapped` sees.
     */
    @Test
    void aNameWrappedRoundARecordReachesItsPositions() {
        Map<String, BoundaryAssessment> lines = linesOf(WRAPPERS, "wrappers");

        assertEquals("invariant Wrapped (min)", lines.get("onWrapped/v.n = 1").origin());
        assertEquals("invariant NonEmptyBag (min)",
                lines.get("onNonEmpty/List.length(v.xs) = 1").origin());
    }

    /**
     * A clause relating two positions places nothing on either, however far it takes their ranges in.
     *
     * <p>The rule this is here to keep. Neither position is divided by it, so an edge derived from it
     * would be a partition of a number the author never bounded (#427).
     */
    @Test
    void aClauseRelatingTwoPositionsPlacesNoEdge() {
        String report = report(MODEL);

        assertTrue(report.contains("""
                  onSpan                   implemented   rows 1    pending 0
                    signature   not applicable (this behavior's output is not a sum)
                    partition   not measured (no partition axis was derived at any position)
                      · not derivable: v.startsAt
                      · not derivable: v.endsAt
                    boundary    not measured (no line was derived at any position)
                """), report);
    }

    /** Nor one bounding a field by another field rather than by a constant. */
    @Test
    void aBoundAgainstAnotherFieldPlacesNoEdge() {
        String report = report(MODEL);

        assertFalse(report.contains("no row is at onFloor/"), report);
        assertTrue(report.contains("""
                  onFloor                  implemented   rows 1    pending 0
                    signature   not applicable (this behavior's output is not a sum)
                    partition   not measured (no partition axis was derived at any position)
                      · not derivable: v.n
                      · not derivable: v.min
                    boundary    not measured (no line was derived at any position)
                """), report);
    }

    /**
     * A range taken in by another position's bound is not an edge.
     *
     * <p>`b <= 10` places an edge on `b`, and `a < b` carries that as far as `a <= 9` — which is
     * where `b` stops and not something any clause said about `a`. Counting the 9 would put back the
     * whole of what the relational rule was excluded for, by the one route a reader that had stopped
     * asking where an edge came from would take.
     */
    @Test
    void aRangeNarrowedByAnotherPositionsBoundIsNotAnEdge() {
        String report = report(MODEL);

        assertTrue(report.contains("no row is at onR/v.b = 10 (invariant R (max))"), report);
        assertFalse(report.contains("no row is at onR/v.a"), report);
    }

    /**
     * The same where the bound is on the other position's own type.
     *
     * <p>The case a reading built out of one clause at a time gets wrong. Seeding `a < b.value`
     * alone still has `B`'s own maximum under it, so `a <= 9` falls out of that clause's own
     * derivation and looks like an edge the clause placed. It is `B`'s edge, reached through `a < b`,
     * and `a` has none.
     */
    @Test
    void aRangeNarrowedThroughAnotherPositionsTypeIsNotAnEdgeEither() {
        String report = report(MODEL);

        assertTrue(report.contains("no row is at onUnder/v.b = 10 (invariant B (max))"), report);
        assertFalse(report.contains("no row is at onUnder/v.a"), report);
    }

    /** The rules written on newtypes are measured as they were. A repair that moved these rather
     *  than adding to them would read as this issue being fixed. */
    @Test
    void theSameRulesOnNewtypesAreMeasuredAsBefore() {
        String report = report(ON_NEWTYPES);

        assertTrue(report.contains(
                "no row is at onName/String.length(v) = 1 (invariant Name (min))"), report);
        assertTrue(report.contains(
                "no row is at onCart/List.length(c) = 1 (invariant Cart (min))"), report);
        assertTrue(report.contains("no row is at onHop/v.n = 1 (invariant Count (min))"), report);
    }

    /**
     * A record clause tighter than the type's own owns the line rather than narrowing it.
     *
     * <p>`Moved`'s clause bounds one coordinate against a constant, so it places an edge of its own,
     * and 5 is where the two intersect. Reported as `Count` narrowed within `Moved` it named the rule
     * that did not put the edge where it is.
     */
    @Test
    void aTighterRecordClauseOwnsTheLineRatherThanNarrowingIt() {
        String report = report(ON_NEWTYPES);

        assertTrue(report.contains("no row is at onMoved/v.n = 5 (invariant Moved (min))"), report);
        assertFalse(report.contains("within Moved"), report);
    }

    /**
     * A position whose type is measured two ways, with rules arriving from outside it.
     *
     * <p>A `String` is the one value with two coordinates — its own order and the length of it — so
     * this is where reading more declarations could change which one a position is measured at.
     */
    private static final String TWO_WAYS = """
            module twoways

            data Name   = String invariant value >= "m"
            data Person = { name: Name } invariant String.length(name.value) >= 3

            data R = { s: String }
                invariant s >= "m"
                invariant String.length(s) >= 3

            data Ok = { size: Int }

            behavior onPerson : (v: Person) -> Ok
                constructs Ok
            let onPerson (v) = Ok { size = String.length(v.name.value) }

            behavior onR : (v: R) -> Ok
                constructs Ok
            let onR (v) = Ok { size = String.length(v.s) }

            example onPerson | (Person { name = Name("zzz") }) -> Ok { size = 3 }
            example onR      | (R { s = "zzz" }) -> Ok { size = 3 }
            """;

    /**
     * A rule from outside states an end and does not choose the coordinate.
     *
     * <p>`Name` is measured on its own order because its own clause is about its value, and a record
     * bounding the length of it says where a length stops without making the length what this
     * position is measured at. Read as a choice, the axis switched: the line at `m` — a rule the
     * author wrote and a report had been printing — went out, and the length edge came in beside
     * nothing saying the other had gone.
     */
    @Test
    void aRuleFromOutsideDoesNotChooseWhichCoordinateAPositionIsMeasuredAt() {
        String report = report(TWO_WAYS);

        assertTrue(report.contains("no row is at onPerson/v.name = m (invariant Name (min))"),
                report);
        assertFalse(report.contains("String.length(v.name"),
                "the record's clause states an end on a coordinate this position is not measured at:\n"
                        + report);
    }

    /**
     * And where the type chose nothing, two such rules choose nothing either.
     *
     * <p>Both coordinates of `s` are bounded and neither by `s`'s own type, so which of them this
     * position is measured at is a question with no answer here (ADR-0090). Left as a position
     * nothing divides, which claims nothing; taking whichever was looked at first would put a line
     * the author can read beside one they cannot see.
     */
    @Test
    void rulesAboutBothCoordinatesLeaveThePositionUndivided() {
        String report = report(TWO_WAYS);

        assertTrue(report.contains("""
                  onR                      implemented   rows 1    pending 0
                    signature   not applicable (this behavior's output is not a sum)
                    partition   not measured (no partition axis was derived at any position)
                      · not derivable: v.s
                    boundary    not measured (no line was derived at any position)
                """), report);
    }

    /**
     * A floor no value of the type reaches, written both ways.
     *
     * <p>A `Set<Bool>` holds two elements at most, so a floor of three is a line nothing stands at.
     * No row can name such a value, which is why nothing here writes one: what the line comes to is
     * asked of the measure, and the measure answers without a row.
     */
    private static final String UNMEETABLE = """
            module unmeetable

            data FlagsN   = Set<Bool>       invariant Set.size(value) >= 3
            data NumbersN = Set<Int>        invariant Set.size(value) >= 3
            data FlagsR   = { s: Set<Bool> } invariant Set.size(s) >= 3
            data NumbersR = { s: Set<Int> }  invariant Set.size(s) >= 3
            data TextR    = { s: String }    invariant String.length(s) >= 3

            data Ok = { size: Int }

            behavior onFlagsN : (v: FlagsN) -> Ok
                constructs Ok
            let onFlagsN (v) = Ok { size = Set.size(v.value) }

            behavior onNumbersN : (v: NumbersN) -> Ok
                constructs Ok
            let onNumbersN (v) = Ok { size = Set.size(v.value) }

            behavior onFlagsR : (v: FlagsR) -> Ok
                constructs Ok
            let onFlagsR (v) = Ok { size = Set.size(v.s) }

            behavior onNumbersR : (v: NumbersR) -> Ok
                constructs Ok
            let onNumbersR (v) = Ok { size = Set.size(v.s) }

            behavior onTextR : (v: TextR) -> Ok
                constructs Ok
            let onTextR (v) = Ok { size = String.length(v.s) }
            """;

    /**
     * A line the record placed is settled the way one on a newtype is.
     *
     * <p>The route an edge arrived by is not evidence about whether a row can be written at it, and
     * this issue adds a second route. A floor of three on a `Set<Bool>` is not known to be writable
     * and stays out of the denominator whichever way it is written; the same floor on a `Set<Int>`
     * is a row somebody owes, also either way. Held because the whole of #649 is that the two
     * spellings state one rule: a repair that made the record's line a counted obligation where the
     * newtype's is not would have granted that rule two meanings again.
     */
    @Test
    void aLineTheRecordPlacedIsSettledLikeOneOnANewtype() {
        Map<String, BoundaryAssessment> lines = new LinkedHashMap<>();
        Compilation compilation = Compilation.ofSource(UNMEETABLE, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        compilation.db().ask(new Adequacy.Coverage("unmeetable")).value()
                .forEach((behavior, evidence) -> evidence.boundaries()
                        .forEach(line -> lines.put(behavior + "/" + line.label(), line)));

        assertEquals(Set.of("onFlagsN/Set.size(v) = 3", "onNumbersN/Set.size(v) = 3",
                        "onFlagsR/Set.size(v.s) = 3", "onNumbersR/Set.size(v.s) = 3",
                        "onTextR/String.length(v.s) = 3"),
                lines.keySet(), "one line each, and the record's is on the count of the field");
        assertFalse(lines.get("onFlagsN/Set.size(v) = 3").writability().known(),
                "two booleans are all there are");
        assertFalse(lines.get("onFlagsR/Set.size(v.s) = 3").writability().known(),
                "and writing the rule on the record does not add a third");
        assertTrue(lines.get("onNumbersN/Set.size(v) = 3").writability().known(),
                "three integers are three integers");
        assertTrue(lines.get("onNumbersR/Set.size(v.s) = 3").writability().known(),
                "and a record holding them is a value that can be built");
    }

    /**
     * Which counts the projection may not stand behind, held at the rule rather than through it.
     *
     * <p>Through the measure there is nothing to hold. A length edge in a model this size is settled
     * by the value the generator builds for it, so it stays counted whether or not the projection was
     * entitled to say so, and an assertion on its verdict would pass with the rule reverted. What
     * shows the difference is a corpus: declining the proof at every count takes twenty
     * `String.length` edges out of the denominator across `souther-examples`, and the suite stays
     * green throughout. So the distinction is pinned where it is decided.
     */
    /**
     * A wrapper whose clause relates two of the record's fields, beside the record without it.
     *
     * <p>Both fields stop at 10 by their own types, and `a < b` leaves `a` stopping at 9 — the
     * interval shape of #427, written one name up. The bare record beside it is the control: an edge
     * that does not move proves nothing unless the same edge moves elsewhere.
     */
    private static final String WRAPPED_RELATION = """
            module wrappedrelation

            data A    = Int invariant value <= 10
            data B    = Int invariant value <= 10
            data Base = { a: A, b: B }

            data Wrapped = Base invariant value.a.value < value.b.value
            data Held    = { w: Wrapped }

            data Ok = { size: Int }

            behavior onWrapped : (v: Wrapped) -> Ok
                constructs Ok
            let onWrapped (v) = Ok { size = v.a.value }

            behavior onBare : (v: Base) -> Ok
                constructs Ok
            let onBare (v) = Ok { size = v.a.value }

            behavior onHeld : (v: Held) -> Ok
                constructs Ok
            let onHeld (v) = Ok { size = v.w.a.value }
            """;

    /**
     * A wrapper's relational clause narrows the record's positions though it places no edge.
     *
     * <p>The half a wrapper read for its ends alone would drop. Such a clause leaves a range and not
     * a line, so a reader taking only the lines from a wrapper keeps `a` stopping at 10 — a value no
     * `Wrapped` holds, and a row asked for that nobody can write. Placing an edge and taking one in
     * are separate acts, and a wrapper does both.
     *
     * <p>The line stays `A`'s and says who took it in, which is what a narrowed origin is for: the
     * wrapper moved the edge and did not draw it.
     */
    @Test
    void aWrappersRelationNarrowsThePositionsItPlacesNoEdgeOn() {
        Map<String, BoundaryAssessment> lines = linesOf(WRAPPED_RELATION, "wrappedrelation");

        assertTrue(lines.containsKey("onBare/v.a = 10"),
                "`a` stops where its own type stops when nothing narrows it: " + lines.keySet());
        assertTrue(lines.containsKey("onWrapped/v.a = 9"),
                "and one step lower under the wrapper's clause: " + lines.keySet());
        assertEquals("invariant A (max) within Wrapped",
                lines.get("onWrapped/v.a = 9").origin(),
                "the wrapper moved the edge `A` drew and did not draw one");
    }

    /**
     * And the declaration that moved it is named wherever the position is reached from.
     *
     * <p>`Held` holds a `Wrapped` and states nothing. The edge is still `A`'s and it was still
     * `Wrapped`'s clause that took it in, so that is what the line says — read off the value the
     * position sits in, it named a declaration with no clause about the pair at all, and a reader
     * following it finds nothing there. The name is part of what tells one line from another
     * ({@link OriginRef.Line}) and not only what is printed.
     */
    @Test
    void aNarrowedEdgeNamesTheDeclarationThatMovedItAndNotTheValueItSitsIn() {
        Map<String, BoundaryAssessment> lines = linesOf(WRAPPED_RELATION, "wrappedrelation");

        assertEquals("invariant A (max) within Wrapped",
                lines.get("onHeld/v.w.a = 9").origin(),
                "the clause is `Wrapped`'s wherever a `Wrapped` is held: " + lines.keySet());
    }

    /** A length floor over an element type nothing inhabits. Its own module, since a declaration that
     *  cannot be built leaves the module with nothing to build against. */
    private static final String UNINHABITED = """
            module uninhabited

            data Loop   = { next: Loop }
            data LoopyR = { xs: List<Loop> } invariant List.length(xs) >= 1

            data Ok = { size: Int }

            behavior onLoopyR : (v: LoopyR) -> Ok
                constructs Ok
            let onLoopyR (v) = Ok { size = List.length(v.xs) }
            """;

    /**
     * A length is not proven by the range where the thing counted may not exist.
     *
     * <p>The end-to-end half of the rule below. One is a number the rules leave and a list of one
     * needs an element, and `Loop` has none — so the range says the count is admissible and says
     * nothing about whether a value holds it. This is the case a rule about distinctness would let
     * through: a list repeats an element, which is only an answer once there is an element.
     */
    @Test
    void aLengthOverSomethingUninhabitedIsNotProvenByTheRange() {
        BoundaryAssessment line = linesOf(UNINHABITED, "uninhabited")
                .get("onLoopyR/List.length(v.xs) = 1");

        assertFalse(line.writability().known(),
                "nothing inhabits `Loop`, so nothing holds a list of one");
    }

    @Test
    void onlyAStringsLengthIsACountEveryValueHas() {
        assertTrue(NumericMeasures.everyCountHasAValue(
                        ValueName.Stdlib.operation("String", "length")),
                "a string of any length is a character repeated");
        assertFalse(NumericMeasures.everyCountHasAValue(
                        ValueName.Stdlib.operation("List", "length")),
                "a list of one needs an element, and a type nothing inhabits has none");
        assertFalse(NumericMeasures.everyCountHasAValue(ValueName.Stdlib.operation("Set", "size")),
                "a set of three needs three that differ");
        assertFalse(NumericMeasures.everyCountHasAValue(ValueName.Stdlib.operation("Map", "size")),
                "and a map of three needs three keys that differ");
    }

    /** Every line one module draws, by the behavior and label it is reported under. */
    private static Map<String, BoundaryAssessment> linesOf(String source, String module) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        Map<String, BoundaryAssessment> lines = new LinkedHashMap<>();
        compilation.db().ask(new Adequacy.Coverage(module)).value()
                .forEach((behavior, evidence) -> evidence.boundaries()
                        .forEach(line -> lines.put(behavior + "/" + line.label(), line)));
        return lines;
    }

    private static String report(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        return AdequacyReport.of(compilation).human(SourceNameResolver.identity());
    }
}
