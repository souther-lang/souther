package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.check.DeclaredSig;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Position;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.numeric.Towards;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;

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

    /** And where nothing narrowed the region at all, which is every item of a border nothing is on
     *  the way to. */
    @Test
    void andWhereNothingNarrowedTheRegionNothingIsProved() {
        assertFalse(realize(pairAt(new Criterion.AtTheLevel(Level.OfTheQuantity.of(1))), region())
                        instanceof Realization.Impossible,
                "the declarations leave the distance every value it has");
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
        Seam parted = Seam.of(space, line, Towards.BELOW);
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

    private static final Read READ = read();

    private static SearchRegion region() {
        return READ.input().quantities(READ.rules()).region();
    }

    private static NumericTerm.FromOnePosition term(String spelled) {
        return new NumericTerm.ValueOf(pathOf(spelled));
    }

    private static TermPath pathOf(String spelled) {
        return READ.input().positions().stream().map(Position::path)
                .filter(each -> each.toString().equals(spelled))
                .findFirst().orElseThrow(() -> new AssertionError(
                        "no position at " + spelled + " among " + READ.input().positions().stream()
                                .map(Position::path).toList()));
    }

    private record Read(InputDomain input, RuleReadingSource rules) {}

    private static Read read() {
        Compilation compilation =
                Compilation.ofSources(List.of(PAIR), souther.compiler.meta.ModulePath.EMPTY);
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Map<String, DeclaredSig> sigs =
                compilation.db().ask(new Bodies.DeclaredSignatures(module)).value();
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        return new Read(InputDomain.of(sigs.get("read"),
                RuleReadingContext.unshared(rules, ReadAs.THE_COMPILATION_DOES)), rules);
    }
}
