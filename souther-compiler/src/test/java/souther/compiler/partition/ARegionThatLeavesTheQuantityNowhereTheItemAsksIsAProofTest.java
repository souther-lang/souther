package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.TestDay;
import souther.compiler.carrier.Membership;
import souther.compiler.check.Carrier;
import souther.compiler.check.DeclaredSig;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.TypeCardinality;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Position;
import souther.compiler.inputs.Quantities;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;
import souther.compiler.numeric.Towards;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import java.math.BigInteger;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where the region leaves the item's quantity no value the item asks for, the item is out of reach
 * and that is proved rather than searched for.
 *
 * <p>The region answers where a quantity runs inside it and an item answers which of that
 * quantity's values stand at it, and putting the two together is the whole of this. Asked apart —
 * the region whether it holds anything at all, the positions one at a time — a contradiction
 * between the way to a border and the border itself is walked for until a figure of this compiler's
 * runs out.
 *
 * <p>Said of each shape of {@link Standing}, because each of them is a separate reader of the two
 * answers and any of them can be the one that does not ask. The shapes differ only in how the
 * quantity is taken out of the item — a coordinate, a distance, a form — and not in what is then
 * asked of it, which is why the same sentence is written three times rather than once over whichever
 * shape a fixture happens to build.
 */
class ARegionThatLeavesTheQuantityNowhereTheItemAsksIsAProofTest {

    /** Two positions with no rule of their own, so everything narrowing them is taken in here. */
    private static final String PAIR = """
            module g

            data Ok

            behavior read : (x: Int, y: Int) -> Ok
            """;

    /**
     * A distance the region stops at nought, asked for at one.
     *
     * <p>Which is what an author writes as two guards one after the other, and what the two together
     * refuse. Neither of them refuses it alone.
     */
    @Test
    void aDistanceTheRegionStopsBelowTheLevelTheItemAsksFor() {
        assertInstanceOf(Realization.Impossible.class,
                realize(pairAt(new Criterion.AtTheLevel(Level.OfTheQuantity.of(1))), yIsNoMoreThanX()),
                "the region leaves `y - x` at nought and below, and the item asks for one");
    }

    /** And the run above that level, which is the other point the same border owes. */
    @Test
    void andTheRunAboveALevelTheRegionStopsAt() {
        assertInstanceOf(Realization.Impossible.class,
                realize(pairAt(above(Level.OfTheQuantity.of(0))), yIsNoMoreThanX()),
                "the region leaves `y - x` at nought and below, and the item asks for more");
    }

    /**
     * The same line handed over as a form, which is what a pair on two orders lowers to.
     *
     * <p>Beside the sentence above and not standing for it. Which of the two a border comes to this
     * as is decided by the positions' orders, so a proof that only one of them can make is a proof
     * an author gets for one model and not for the model beside it.
     */
    @Test
    void theSameLineAskedAsAForm() {
        assertInstanceOf(Realization.Impossible.class,
                realize(formAt(new Criterion.AtTheLevel(Level.OfTheQuantity.of(1))), yIsNoMoreThanX()),
                "the form `y - x` runs at nought and below, and the item asks for one");
    }

    /** And one coordinate, where the region and the item speak of the position itself. */
    @Test
    void oneCoordinateAtAValueTheRegionRefuses() {
        assertInstanceOf(Realization.Impossible.class,
                realize(oneAt(level(5)), xIsNoMoreThanNought()),
                "the region leaves `x` at nought and below, and the item asks for five");
    }

    /**
     * And where the two do meet, nothing here answers.
     *
     * <p>The control, and it is written as what this must not do rather than as what the search
     * comes back with. A region that admits the level leaves the question exactly where it was: the
     * search may find a row or run out of what it is allowed, and either is an answer this is not
     * entitled to improve on. Written as {@code Found}, the control would be pinning what the search
     * happens to manage today — and a run of an order the values step past meets the item and holds
     * nothing, which is a proof nobody here has made.
     */
    @Test
    void whereTheTwoMeetNothingIsProved() {
        assertFalse(realize(pairAt(new Criterion.AtTheLevel(Level.OfTheQuantity.of(0))), yIsNoMoreThanX())
                        instanceof Realization.Impossible,
                "the region leaves `y - x` at nought, which is the level the item asks for");
        assertFalse(realize(formAt(new Criterion.AtTheLevel(Level.OfTheQuantity.of(0))), yIsNoMoreThanX())
                        instanceof Realization.Impossible,
                "and the same of the form");
        assertFalse(realize(oneAt(level(0)), xIsNoMoreThanNought())
                        instanceof Realization.Impossible,
                "and of the coordinate, which the region leaves standing at nought");
    }

    /**
     * A pair on an order that counts nothing is not asked at all.
     *
     * <p>The other way this proves nothing, and it is not the two runs meeting. Two strings stand no
     * measurable distance apart, so the one level such a quantity takes is the one where they meet
     * and a point of it asks which way round they stand — while what the region has to say about
     * the pair is arithmetic over positions that add up. The two are not one order, and a crossing
     * that took them for one would compare a side against a bound and read whatever came back as a
     * proof.
     *
     * <p>Written against a region that does bound the pair, which is what makes the answer the
     * shape's rather than the bounds': handed an open region, a crossing that mixed the two
     * vocabularies would answer this correctly for the wrong reason.
     */
    @Test
    void aPairOnAnOrderThatCountsNothingIsNotAsked() {
        Standing strings = new Standing.OfTwoOnOneCarrier(term("y"), term("x"), Carrier.TEXT,
                new Criterion.AtTheLevel(Level.OfTheQuantity.of(1)));

        assertFalse(realize(strings, yIsNoMoreThanX()) instanceof Realization.Impossible,
                "what the region says of a distance is not what this item asks about a pair");
    }

    /**
     * And every shape names a quantity, which is what the crossing is of.
     *
     * <p>Here because the property above rests on it: a shape whose quantity weighs no term is a
     * question about nothing, and asked of a region it comes back as an answer about a form rather
     * than about an item. Refused where such a shape is built, so the crossing has no case for it.
     */
    @Test
    void andEveryShapeNamesAQuantity() {
        assertThrows(IllegalArgumentException.class,
                () -> new Standing.OfTwoOnOneCarrier(term("x"), term("x"), Carrier.WHOLE,
                        new Criterion.AtTheLevel(Level.OfTheQuantity.of(0))),
                "a distance is between two positions");
        assertThrows(IllegalArgumentException.class,
                () -> new Standing.OfAForm(form(0, 0, 1), Map.of(),
                        LevelSpace.steppingBy(ExactRatio.ONE),
                        new Criterion.AtTheLevel(Level.OfTheQuantity.of(0))),
                "a form stands over the positions it names");
    }

    /**
     * And what a division leaves of a form: where the values the region leaves the form have no
     * member of the class a remainder names, the remainder is out of reach, and where they have one
     * it is not.
     *
     * <p>The form is held at nought by the region, so it leaves nought and nothing else by seven.
     * Asked for three the walk of the class is of no member and ends, which is the proof; asked for
     * nought it finds the one.
     */
    @Test
    void aRemainderOfAFormTheRegionLeavesNoMemberOfIsOutOfReach() {
        SearchRegion holdingNought = region().assuming(form(1, 0, 0), Rel.EQ).taken()
                .assuming(form(0, 1, 0), Rel.EQ).taken();

        assertInstanceOf(Realization.Impossible.class,
                realize(remainderAt(3), holdingNought),
                "the form stands at nought, which leaves nought by seven and not three");
        assertFalse(realize(remainderAt(0), holdingNought) instanceof Realization.Impossible,
                "and nought is the remainder it does leave");
    }

    /**
     * A hole the region holds in the distance, against the level the item asks for.
     *
     * <p>The run the region projects the distance onto has no hole in it, so crossing runs leaves the
     * level reachable. The region itself holds the hole, and asked to take the level in finds the
     * contradiction — which is also so of a form written at twice the weight, the same relation in
     * other numbers.
     */
    @Test
    void aHoleTheRegionHoldsAtTheLevelTheItemAsksForIsOutOfReach() {
        SearchRegion apart = region().assuming(form(-1, 1, 0), Rel.NE).taken();
        SearchRegion apartAtTwiceTheWeight = region().assuming(form(-2, 2, 0), Rel.NE).taken();
        Criterion atNought = new Criterion.AtTheLevel(Level.OfTheQuantity.of(0));

        assertInstanceOf(Realization.Impossible.class, realize(pairAt(atNought), apart),
                "the region keeps `y - x` away from nought, and the item asks for nought");
        assertInstanceOf(Realization.Impossible.class,
                realize(pairAt(atNought), apartAtTwiceTheWeight),
                "and the relation is the same in whatever weight it is written");
        assertInstanceOf(Realization.Impossible.class, realize(formAt(atNought), apart),
                "and of the same line handed over as a form");
    }

    /**
     * An item of two runs is out of reach only where each of them is.
     *
     * <p>Minus two to two with nought taken out is the run below nought and the run above it. A
     * region keeping the distance above nought holds nothing of the first and something of the
     * second, and an item with one run out of reach is not out of reach; a region holding the
     * distance at nought holds nothing of either.
     */
    @Test
    void anItemOfTwoRunsIsOutOfReachOnlyWhereEveryRunIs() {
        Criterion eitherSideOfNought = new Criterion.Within(
                new Band(Band.endAt(null, Bound.at(Level.OfTheQuantity.of(-2), true), Towards.ABOVE),
                        Band.endAt(null, Bound.at(Level.OfTheQuantity.of(2), true), Towards.BELOW)),
                Level.OfTheQuantity.of(0), Towards.ABOVE);

        assertFalse(realize(pairAt(eitherSideOfNought),
                        region().assuming(form(-1, 1, 0), Rel.GT).taken())
                        instanceof Realization.Impossible,
                "the region leaves the distance above nought, which the second run asks for");
        assertInstanceOf(Realization.Impossible.class,
                realize(pairAt(eitherSideOfNought),
                        region().assuming(form(-1, 1, 0), Rel.EQ).taken()),
                "and with the distance held at nought neither run has a value");
    }

    /**
     * And what two numbers come to multiplied: where the region leaves the first factor no value
     * dividing the level the item asks for, every pair multiplying to it is one the region refuses,
     * and the product is out of reach; where it leaves one, it is not.
     *
     * <p>The region holds {@code x} at two. Seven is no multiple of two, so every pair of its
     * divisors puts {@code x} somewhere else; six is two times three. Held at minus two, six is
     * minus two times minus three, which a walk of the divisors above nought alone would miss.
     */
    @Test
    void aProductTheRegionLeavesNoPairOfIsOutOfReach() {
        SearchRegion atTwo = region().assuming(form(1, 0, -2), Rel.EQ).taken();
        SearchRegion atMinusTwo = region().assuming(form(1, 0, 2), Rel.EQ).taken();

        assertInstanceOf(Realization.Impossible.class, realize(productAt(7), atTwo),
                "the first factor stands at two, which divides no pair multiplying to seven");
        assertFalse(realize(productAt(6), atTwo) instanceof Realization.Impossible,
                "and six is two times three");
        assertFalse(realize(productAt(6), atMinusTwo) instanceof Realization.Impossible,
                "and minus two times minus three");
    }

    /**
     * And what {@code x} leaves divided by {@code y}: where the region holds the divisor at three,
     * a remainder of five is one no pair gives, since a remainder is below its divisor in size, and
     * is out of reach; a remainder of two is not.
     */
    @Test
    void aRemainderTheRegionLeavesNoDivisorForIsOutOfReach() {
        SearchRegion atThree = region().assuming(form(0, 1, -3), Rel.EQ).taken();

        assertInstanceOf(Realization.Impossible.class, realize(remainderByAnInputAt(5), atThree),
                "the divisor stands at three, which no remainder of five is below");
        assertFalse(realize(remainderByAnInputAt(2), atThree) instanceof Realization.Impossible,
                "and two is below three");
    }

    /**
     * A remainder is below its divisor in size, and the divisors are numbers of the type: nothing
     * leaves the greatest {@code Int} or the least, since each would need a divisor one past an
     * end, and a divisor at the least {@code Int} leaves the remainder one above it.
     */
    @Test
    void aRemainderNoDivisorOfTheTypeLeavesIsOutOfReach() {
        SearchRegion free = region();

        assertInstanceOf(Realization.Impossible.class,
                realize(remainderByAnInputAt(Long.MAX_VALUE), free),
                "the divisor would be one past the greatest Int");
        assertInstanceOf(Realization.Impossible.class,
                realize(remainderByAnInputAt(Long.MIN_VALUE), free),
                "and the least needs one below the least");
        assertFalse(realize(remainderByAnInputAt(Long.MIN_VALUE + 1), free)
                instanceof Realization.Impossible, "the least Int itself leaves the next one up");
        assertFalse(realize(remainderByAnInputAt(Long.MAX_VALUE - 1), free)
                instanceof Realization.Impossible, "and the greatest leaves one below it");
    }

    /**
     * Where the divisors tried are all there is room for and the rules still refuse every one, the
     * item is left open and not proved out of reach: the divisors past the figure were not asked.
     * With the dividend held at nought nothing is a remainder of one but a divisor of one, which
     * is none above one.
     */
    @Test
    void aSearchThatRanOutOfDivisorsProvesNothing() {
        SearchRegion atNought = region().assuming(form(1, 0, 0), Rel.EQ).taken();

        assertInstanceOf(Realization.Unknown.class,
                realize(remainderByAnInputAt(1), atNought),
                "no divisor tried leaves one, and the ones past the figure were not tried");
    }

    /** What {@code x} leaves divided by {@code y}, at one of the remainders. */
    private static Standing remainderByAnInputAt(long remainder) {
        Map<NumericTerm, Carrier> on = new LinkedHashMap<>();
        on.put(term("x"), Carrier.WHOLE);
        on.put(term("y"), Carrier.WHOLE);
        return new Standing.OfARemainderByAnInput(term("x"), term("y"), on,
                LevelSpace.steppingBy(ExactRatio.ONE),
                new Criterion.AtTheLevel(Level.OfTheQuantity.of(remainder)));
    }

    /** What {@code x} and {@code y} come to multiplied, at one of the products. */
    private static Standing productAt(long product) {
        Map<NumericTerm, Carrier> on = new LinkedHashMap<>();
        on.put(term("x"), Carrier.WHOLE);
        on.put(term("y"), Carrier.WHOLE);
        return new Standing.OfAProduct(term("x"), term("y"), on,
                LevelSpace.steppingBy(ExactRatio.ONE),
                new Criterion.AtTheLevel(Level.OfTheQuantity.of(product)));
    }

    /**
     * A remainder of a form together with another number the region leaves nowhere the level asks
     * for is out of reach.
     *
     * <p>Held at nought, {@code x} leaves nought by seven and {@code y} is nought, so the sum is
     * nought and not three. The remainders the added number can make up three with are the ones it
     * leaves, and none is one the region leaves {@code x}.
     */
    @Test
    void aRemainderPlusANumberTheRegionLeavesNoSumOfIsOutOfReach() {
        SearchRegion holdingNought = region().assuming(form(1, 0, 0), Rel.EQ).taken()
                .assuming(form(0, 1, 0), Rel.EQ).taken();

        assertInstanceOf(Realization.Impossible.class,
                realize(remainderPlusAt(3), holdingNought),
                "both stand at nought, which sum to nought and not three");
        assertFalse(realize(remainderPlusAt(0), holdingNought) instanceof Realization.Impossible,
                "and nought is the sum they do come to");
    }

    /** The remainder of {@code x} by seven plus {@code y}, at one of the sums. */
    private static Standing remainderPlusAt(long sum) {
        return new Standing.OfARemainderAndAForm(form(1, 0, 0), Map.of(term("x"), Carrier.WHOLE),
                BigInteger.valueOf(7), form(0, 1, 0), Map.of(term("y"), Carrier.WHOLE),
                LevelSpace.steppingBy(ExactRatio.ONE),
                new Criterion.AtTheLevel(Level.OfTheQuantity.of(sum)));
    }

    /** A remainder of {@code x + y} by seven, at one of the remainders. */
    private static Standing remainderAt(long remainder) {
        Map<NumericTerm, Carrier> on = new LinkedHashMap<>();
        on.put(term("x"), Carrier.WHOLE);
        on.put(term("y"), Carrier.WHOLE);
        return new Standing.OfARemainder(form(1, 1, 0), on, LevelSpace.steppingBy(ExactRatio.ONE),
                BigInteger.valueOf(7),
                new Criterion.AtTheLevel(Level.OfTheQuantity.of(remainder)));
    }

    /** And where nothing narrowed the region at all, which is every item of a border nothing is on
     *  the way to. */
    @Test
    void andWhereNothingNarrowedTheRegionNothingIsProved() {
        assertFalse(realize(pairAt(new Criterion.AtTheLevel(Level.OfTheQuantity.of(1))), region())
                        instanceof Realization.Impossible,
                "the declarations leave the distance every value it has");
    }

    /**
     * A region that leaves the elements of a container nowhere proves no count out of reach.
     *
     * <p>Where no value is an element, the container holds none, and a container holding none has
     * none of its elements meeting a statement: a count of none is reached. The elements' numbers
     * are chosen by the composing and asked nowhere, so what the region leaves them settles
     * nothing.
     */
    @Test
    void aContainerHoldingNothingIsACountOfNone() {
        Quantities measuring = COUNTED.input().quantities(COUNTED.rules());
        SearchRegion holdingNothing = measuring.region();
        TermPath xs = pathIn(COUNTED, "xs");
        NumericTerm element = new NumericTerm.ValueOf(xs.element());
        // An element above the limit: `limit - x >= 0` failing, written facing the way a relation
        // over the two faces.
        Map<Quantity, ExactRatio> atMost = new LinkedHashMap<>();
        atMost.put(new DecisionAtom.OfTheInput(new NumericTerm.ValueOf(pathIn(COUNTED, "limit"))),
                ExactRatio.ONE);
        atMost.put(new DecisionAtom.OfTheInput(element), ExactRatio.ONE.negated());
        CountedElements counted = CountedElements.of("counted", new Quantity.HowManyMeet(
                new DecisionSubject.AnInput(xs),
                new Proposition.Compared(new Relation.Affine(
                        new LinearForm<>(ExactRatio.ZERO, atMost), Rel.GE), false)), measuring,
                AnElementMeeting.UNREAD);
        assertTrue(holdingNothing.emptiness().isEmpty(),
                () -> "the region admits rows: " + holdingNothing.emptiness());
        assertInstanceOf(NumericDomain.FormProjection.NothingIsLeft.class,
                holdingNothing.projectionOf(element), "and leaves an element of `xs` nowhere");
        Standing none = new Standing.OfACount(counted, counted.numbers(),
                new Criterion.AtTheLevel(Level.OfTheQuantity.of(0)));
        assertFalse(realize(none, holdingNothing) instanceof Realization.Impossible,
                "a container holding nothing has none of its elements above the limit");
    }

    /**
     * And the same count with a number added to it: the elements are the composing's to choose and
     * the number is placed beside them, so a region that leaves the elements nowhere proves nothing
     * about where the sum can come to.
     */
    @Test
    void aContainerHoldingNothingIsACountOfNoneWithANumberAddedToIt() {
        Quantities measuring = COUNTED.input().quantities(COUNTED.rules());
        SearchRegion holdingNothing = measuring.region();
        TermPath xs = pathIn(COUNTED, "xs");
        NumericTerm element = new NumericTerm.ValueOf(xs.element());
        NumericTerm limit = new NumericTerm.ValueOf(pathIn(COUNTED, "limit"));
        Map<Quantity, ExactRatio> atMost = new LinkedHashMap<>();
        atMost.put(new DecisionAtom.OfTheInput(limit), ExactRatio.ONE);
        atMost.put(new DecisionAtom.OfTheInput(element), ExactRatio.ONE.negated());
        CountedElements counted = CountedElements.of("counted", new Quantity.HowManyMeet(
                new DecisionSubject.AnInput(xs),
                new Proposition.Compared(new Relation.Affine(
                        new LinearForm<>(ExactRatio.ZERO, atMost), Rel.GE), false)), measuring,
                AnElementMeeting.UNREAD);
        Map<NumericTerm, ExactRatio> added = new LinkedHashMap<>();
        added.put(limit, ExactRatio.ONE.negated());
        Standing none = new Standing.OfACountAndAForm(counted,
                new LinearForm<>(ExactRatio.ZERO, added), Map.of(limit, Carrier.WHOLE),
                LevelSpace.steppingBy(ExactRatio.ONE),
                new Criterion.AtTheLevel(Level.OfTheQuantity.of(0)));
        assertFalse(realize(none, holdingNothing) instanceof Realization.Impossible,
                "a container holding nothing has none of its elements above the limit");
    }

    /** The item's line, as far as a row for it is concerned. */
    private static Realization realize(Standing standing, SearchRegion within) {
        return new LevelRealizer().realize(standing, within,
                NothingTheDeclarationsRefuse.at(pathOf("x"), pathOf("y")));
    }

    /** {@code y - x}, as the distance between two positions on one order. */
    private static Standing pairAt(Criterion where) {
        return new Standing.OfTwoOnOneCarrier(term("y"), term("x"), Carrier.WHOLE, where);
    }

    /** The same distance, as the form a pair on two orders is searched for by. */
    private static Standing formAt(Criterion where) {
        Map<NumericTerm, Carrier> on = new LinkedHashMap<>();
        on.put(term("x"), Carrier.WHOLE);
        on.put(term("y"), Carrier.WHOLE);
        return new Standing.OfAForm(form(-1, 1, 0), on,
                LevelSpace.steppingBy(ExactRatio.ONE), where);
    }

    /** And {@code x} itself, which is the quantity of a border on one coordinate. */
    private static Standing oneAt(Criterion where) {
        return new Standing.OfOneCoordinate(term("x"), Carrier.WHOLE, where);
    }

    /** The values of the quantity above one of its levels, which is what a point beside a line
     *  asks for. */
    private static Criterion above(Level line) {
        LevelSpace space = LevelSpace.steppingBy(ExactRatio.ONE);
        Seam parted = HeldSeams.of(space, line, Towards.BELOW);
        return new Criterion.Within(
                new Band(Band.endAt(parted, null, Towards.ABOVE),
                        Band.endAt(null, null, Towards.BELOW)),
                null, Towards.ABOVE);
    }

    /** One value of a coordinate, which is what a level of that quantity is. */
    private static Criterion level(long at) {
        return new Criterion.AtTheLevel(new Level.OnACarrier(Carrier.WHOLE, Count.of(at)));
    }

    /** The region with {@code y <= x} taken in, which admits pairs and no distance above nought. */
    private static SearchRegion yIsNoMoreThanX() {
        return region().assuming(form(-1, 1, 0), Rel.LE).taken();
    }

    /** And the region with {@code x <= 0} taken in, which is the same fact about one position. */
    private static SearchRegion xIsNoMoreThanNought() {
        return region().assuming(form(1, 0, 0), Rel.LE).taken();
    }

    /** {@code cx·x + cy·y + k} over the two positions the behavior declares. */
    private static LinearForm<NumericTerm> form(long cx, long cy, long k) {
        Map<NumericTerm, ExactRatio> coefs = new LinkedHashMap<>();
        if (cx != 0) {
            coefs.put(term("x"), ExactRatio.of(cx));
        }
        if (cy != 0) {
            coefs.put(term("y"), ExactRatio.of(cy));
        }
        return new LinearForm<>(ExactRatio.of(k), coefs);
    }

    private static final Read READ = read(PAIR, "read");

    /**
     * A container whose elements no value is — so it holds none — and a number beside them.
     */
    private static final Read COUNTED = read("""
            module g

            data Ok

            data Never = Int
                invariant value >= 1 && value <= 0

            behavior counted : (xs: List<Never>, limit: Int) -> Ok
            """, "counted");

    private static SearchRegion region() {
        return READ.input().quantities(READ.rules()).region();
    }

    private static NumericTerm.FromOnePosition term(String spelled) {
        return new NumericTerm.ValueOf(pathOf(spelled));
    }

    private static TermPath pathOf(String spelled) {
        return pathIn(READ, spelled);
    }

    private static TermPath pathIn(Read read, String spelled) {
        return read.input().positions().stream().map(Position::path)
                .filter(each -> each.toString().equals(spelled))
                .findFirst().orElseThrow(() -> new AssertionError(
                        "no position at " + spelled + " among " + read.input().positions().stream()
                                .map(Position::path).toList()));
    }

    private record Read(InputDomain input, RuleReadingSource rules) {}

    private static Read read(String source, String behavior) {
        Compilation compilation =
                Compilation.ofSources(List.of(source), souther.compiler.meta.ModulePath.EMPTY);
        String module = compilation.modules().get(0);
        Map<String, DeclaredSig> sigs =
                compilation.db().ask(new Bodies.DeclaredSignatures(module)).value();
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        RuleReadingContext reading =
                RuleReadingContext.unshared(rules, ReadAs.THE_COMPILATION_DOES, TestDay.TODAY);
        return new Read(InputDomain.of(sigs.get(behavior), reading,
                TypeCardinality.Counts.workedOutIn(reading), Membership.none()), rules);
    }
}
