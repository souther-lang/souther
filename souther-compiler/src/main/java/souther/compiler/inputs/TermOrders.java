package souther.compiler.inputs;

import souther.compiler.check.Carrier;
import souther.compiler.numeric.Place;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.TypeSymbol;
import souther.compiler.values.Value;

import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.function.Function;

/**
 * The two orders one term stands on: the one a value of it is observed on, and the one the number it
 * answers is measured on.
 *
 * <p>Two and not one. For a term that is a location's own content they are the same order and there
 * was nothing to tell apart; for a term that is what an operation answered they are the operation's
 * two ends — {@code Date.year(d)} is read off a value counted in days and answers a number counted
 * by one. Held as a single {@code Carrier}, a reader had whichever of the two whoever built it
 * happened to mean, and the one it was not is the one that says nothing when it is wrong: a boundary
 * measured on the argument's order is sharpened onto a value the term never takes, and a row decoded
 * on the answer's order is read as a number the model never named (#1027).
 *
 * <p>Which is the same lesson {@link Carrier} records one size up. Reading a rule and writing a
 * value were two types there while a {@code Time} could be read and not written, and the two agreed
 * with each other and with nothing else. The repair was to hold both ends of one crossing together,
 * and this holds both ends of one term together for the same reason.
 *
 * <p><b>Read anywhere and made in one place.</b> Which orders a term stands on follows from where
 * the reading of an input has that term standing, so a pair put together outside this package is a
 * pair about no reading in particular — and a pair whose halves came from two callers is one whose
 * two ends are free to part. Neither is a class of mistake a reader can see, so neither is a state
 * this lets anything reach: the way to one of these is {@link Quantities#ordersOf}. A test that
 * wants a synthetic pair writes one in this package, where the source set says it is a test.
 */
public final class TermOrders {

    private final NumericTerm term;
    private final Carrier observed;
    private final Carrier answered;
    private final Map<ElementProjection, Carrier> fields;
    private final Map<ElementProjection, List<TypeSymbol>> worn;

    /**
     * @param term     the number these are the orders of. Carried, because an answer that leaves
     *                 the reading and cannot say what it is an answer about is one any reader may
     *                 put beside any term — and two carriers say nothing about which question they
     *                 came from
     * @param observed what a value at the term's path is decoded on, or null where nothing orders
     *                 it — a container has no order and is read by what it holds
     * @param answered what the number the term names is measured on, which is what a boundary on it
     *                 is drawn and written back on
     */
    TermOrders(NumericTerm term, Carrier observed, Carrier answered) {
        this(term, observed, answered, Map.of(), Map.of());
    }

    /**
     * @param fields   for a term over what a walk computed of each element: what each field the
     *                 computation reads is decoded on. Nothing for any other term, which reads no
     *                 field of an element
     * @param worn     for a term read off the places of an element: the names the declaration puts
     *                 at each place on the way to them, the element itself among them, where it
     *                 puts any. A newtype is no step, so a value there may be written inside them,
     *                 and only the declaration says which they are
     */
    TermOrders(NumericTerm term, Carrier observed, Carrier answered,
               Map<ElementProjection, Carrier> fields,
               Map<ElementProjection, List<TypeSymbol>> worn) {
        if (term == null) {
            throw new IllegalArgumentException("orders of no term, which is an answer to nothing");
        }
        this.term = term;
        this.observed = observed;
        this.answered = answered;
        this.fields = Map.copyOf(fields);
        this.worn = Map.copyOf(worn);
    }

    /** The number these are the orders of. */
    public NumericTerm term() {
        return term;
    }

    /**
     * That {@code asked} is the number these are the orders of.
     *
     * <p>For the readers that hold a term beside a pair because their own shape needs the narrower
     * type. Two components are two things to get right, and this is where the second is refused
     * rather than carried into a document.
     */
    public void areOf(NumericTerm asked) {
        if (!term.equals(asked)) {
            throw new IllegalArgumentException("these are the orders of " + term
                    + ", and they are held beside " + asked);
        }
    }

    /**
     * The number this term names at {@code value}, or why there is none.
     *
     * <p>Asked of the answer and not of the term, because reading takes both and an entry taking
     * both is one any caller can hand a term and another term's orders. Here the two arrived
     * together from the reading that settled them.
     */
    public NumericTerm.Reading read(souther.compiler.observe.ObservedValue value) {
        if (term.atOnePosition() == null) {
            throw new IllegalArgumentException(
                    term + " is read over the values of a run, and this is one value");
        }
        return TermReading.at(this, value);
    }

    /**
     * The number this term reads of {@code written}, a value a rule names at the term's position —
     * or null where that is no value of the order a value there is observed on.
     *
     * <p>Read as a row holding the value would be read: the value is put on the order a value at
     * the position is observed on, and the term is read of what stands there. So what a number
     * taken of the position comes to is what {@link #read} says of a row, and nothing here works
     * out a length or a remainder a second time.
     */
    public NumericTerm.Reading readOf(Value written) {
        Place at = observed == null || term.atOnePosition() == null ? null
                : observed.placeOf(written);
        return at == null ? null : read(observed.valueOf(at));
    }

    /** The term, for a reader of a number of an element read off the elements beside it. */
    public NumericTerm.OfAnElementsNeighbours amongItsNeighbours() {
        if (!(term instanceof NumericTerm.OfAnElementsNeighbours among)) {
            throw new IllegalArgumentException(term + " is a number of no element's neighbours");
        }
        return among;
    }

    /**
     * The elements of one occurrence of the container a term read off an element's neighbours is
     * taken over, put together once for the number of any of them — or every element of the run a
     * term gathers under keys ({@link NumericTerm.GatheredUnderItsKey}), every occurrence's.
     *
     * <p>Each element is handed as what it holds at each way into it. Whatever is asked of it is
     * what the number of an element asks and no more, and an element is asked only when some
     * number needs it: how often a value occurs reads every element's value, and the end of a
     * key's values, or what they come to, reads every element's key and the values of that key's
     * elements alone, the first time that key is asked about.
     *
     * @param each every element of the occurrence, or of the run, in the order they are held
     */
    public <G> ElementsTogether<G> together(List<Function<ElementProjection, Holding<G>>> each) {
        return TermReading.together(this, each);
    }

    /**
     * The elements of the run a term gathers under a key an input holds ({@link
     * NumericTerm.GatheredUnderAKey}), every occurrence's, put together once for the number of
     * any key asked.
     *
     * @param each every element of the run, in the order they are held
     */
    public <G> ElementsUnderAKey<G> togetherUnderAKey(
            List<Function<ElementProjection, Holding<G>>> each) {
        return TermReading.togetherUnderAKey(this, each);
    }

    /**
     * What an element holds at a way into it: a value, or nothing, for a reason in the words of
     * whoever handed the element over.
     *
     * <p>Nothing is an answer the caller has and this does not. A row that wrote nothing there and
     * a walk that could not reach the place are two things to a row, and a value of another shape
     * is a third to a read-back; the number only says which nothing it came to first.
     */
    public sealed interface Holding<G> {

        record Value<G>(ObservedValue value) implements Holding<G> {

            public Value {
                Objects.requireNonNull(value, "a value held is a value");
            }
        }

        record Nothing<G>(G why) implements Holding<G> {

            public Nothing {
                Objects.requireNonNull(why, "holding nothing says why");
            }
        }
    }

    /** The elements of one occurrence, put together ({@link #together}). */
    public interface ElementsTogether<G> {

        /**
         * The number {@code own}, one of the elements, reads among them.
         *
         * <p>What stops it is the first thing its reading asks that holds nothing — its own value
         * and then every element's, or its own key and then each key and each value of its key
         * in the order the elements stand, up to the first of those values that was not read —
         * and failing that, what the number's own reading of the values says.
         */
        Neighbouring<G> numberOf(Function<ElementProjection, Holding<G>> own);
    }

    /** The elements of a run put together ({@link #togetherUnderAKey}). */
    public interface ElementsUnderAKey<G> {

        /**
         * What the elements of the key {@code asked}, a value an input holds, come to.
         *
         * <p>What stops it is the first element in order whose key holds nothing or is read as no
         * number, as it stops every key; then the first of the key's own elements, in order, that
         * stops its number. A key no element has comes to no number, which is a reading and not a
         * stop.
         */
        Neighbouring<G> numberUnder(ObservedValue asked);
    }

    /** A number read among an element's neighbours, or the nothing its reading came to first. */
    public sealed interface Neighbouring<G> {

        record Read<G>(NumericTerm.Reading reading) implements Neighbouring<G> {}

        record HeldNothing<G>(G why) implements Neighbouring<G> {}
    }

    /**
     * The same, over the values of a run.
     *
     * <p>Which rows there are and how many values stand at a place in one are the measure's; a term
     * only says what its number is of them.
     */
    public NumericTerm.Reading readOver(List<ObservedValue> values) {
        if (!(term instanceof NumericTerm.TakenOver over)) {
            throw new IllegalArgumentException(term + " is a number of one value, not of a run");
        }
        if (over.source() instanceof RunSource.ComputedOccurrences) {
            throw new IllegalArgumentException(term + " is computed of each element, and values"
                    + " gathered apart from their elements would pair one element's with another's");
        }
        return TermReading.over(this, values);
    }

    /** How often {@code own}, one of the values of a run, occurs among {@code values}, all of
     *  them ({@link #readEachAmong}). */
    public NumericTerm.Reading readAmong(ObservedValue own, List<ObservedValue> values) {
        if (!(term instanceof NumericTerm.OccurrencesOfItsValue
                || term instanceof NumericTerm.OccurrencesOfAKey)) {
            throw new IllegalArgumentException(term + " is no count of how often a value occurs"
                    + " in a run");
        }
        return TermReading.occurrencesOf(this, own, values);
    }

    /**
     * How often each of the values of a run occurs among all of them: one reading for each value,
     * in the order they are given.
     *
     * <p>The values of every occurrence of the place the term counts, gathered across the
     * containers they stand in ({@link NumericTerm.OccurrencesOfItsValue}).
     */
    public List<NumericTerm.Reading> readEachAmong(List<ObservedValue> values) {
        if (!(term instanceof NumericTerm.OccurrencesOfItsValue)) {
            throw new IllegalArgumentException(term + " is no count of how often a value occurs"
                    + " in a run");
        }
        return TermReading.occurrencesAmong(this, values);
    }

    /**
     * The same, over a run computed of each element: one reading per element, each answering what
     * stands at a field of that element.
     */
    public NumericTerm.Reading readOverElements(
            List<Function<ElementProjection, ObservedValue>> each) {
        if (!(term instanceof NumericTerm.TakenOver over)
                || !(over.source() instanceof RunSource.ComputedOccurrences)) {
            throw new IllegalArgumentException(term + " is not computed of each element");
        }
        return TermReading.overElements(this, each);
    }

    /** What the value at {@code field} of an element is decoded on, for a term computed of each
     *  element, or null where nothing orders it. */
    public Carrier fieldCarrier(ElementProjection field) {
        return fields.get(field);
    }

    /** The names the declaration puts at {@code place} of an element, outermost first; none where
     *  it puts none there. */
    public List<TypeSymbol> wornAt(ElementProjection place) {
        return worn.getOrDefault(place, List.of());
    }

    /**
     * What stands at {@code place} of {@code element}, walked through the names the declaration puts
     * on the way ({@link ElementProjection#in}).
     */
    public ObservedValue in(ElementProjection place, ObservedValue element) {
        return place.in(element, this::wornAt);
    }

    /** What a value at the term's path is decoded on, or null where nothing orders it. */
    public Carrier observed() {
        return observed;
    }

    /** What the number the term names is measured on. */
    public Carrier answered() {
        return answered;
    }

    /**
     * Two of these are one where they are the orders of one term.
     *
     * <p>The term among them, because these are an answer and not a pair of carriers: what a string
     * is measured at and what a whole number at another position is measured at come to the same two
     * orders and are answers to two questions. A reader that wants the carriers alone compares
     * those.
     */
    @Override
    public boolean equals(Object other) {
        return other instanceof TermOrders that
                && term.equals(that.term)
                && Objects.equals(observed, that.observed)
                && Objects.equals(answered, that.answered)
                && fields.equals(that.fields)
                && worn.equals(that.worn);
    }

    @Override
    public int hashCode() {
        return Objects.hash(term, observed, answered, fields, worn);
    }

    @Override
    public String toString() {
        return "TermOrders[" + term + " observed=" + observed + ", answered=" + answered + "]";
    }
}
