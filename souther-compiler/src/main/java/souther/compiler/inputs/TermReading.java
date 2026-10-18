package souther.compiler.inputs;

import souther.compiler.check.Carrier;
import souther.compiler.check.Extreme;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.DateTranslation;
import souther.compiler.numeric.Dates;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.UnheldNumber;
import souther.compiler.numeric.ValueTransformation;
import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.ObservedValue;
import souther.compiler.semantics.Arithmetic;
import souther.compiler.semantics.CodePointClass;
import souther.compiler.semantics.TakenArguments;
import souther.compiler.semantics.TakenAs;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.function.Function;

import souther.compiler.inputs.NumericTerm.Reading;
import souther.compiler.inputs.TermOrders.ElementsTogether;
import souther.compiler.inputs.TermOrders.Holding;
import souther.compiler.inputs.TermOrders.Neighbouring;
import net.unit8.notation199x.ScalarValues;

/**
 * The number a term names at an observation of its position, or why there is none.
 *
 * <p>The one reader. What a class asks of a row, what a boundary asks of it, and what a report
 * prints were three walks down a value that agreed only because they were written the same way.
 *
 * <p>Not reachable from a term, which is why it is here rather than on one. Reading takes a term
 * and the orders its number is measured on, and an entry that takes the two as arguments is one any
 * caller can hand a term and another term's orders — the pairing this whole reading exists to stop,
 * one layer along. The way in is {@link TermOrders#read}, which is asked of an answer that already
 * says which term it is of.
 */
final class TermReading {

    private TermReading() { }

    /**
     * The orders are the reading's rather than guessed at from the observation. A written temporal
     * says nothing about whether the position counts days or seconds — the declared type says it —
     * and a reader that sniffed the text for a {@code T} answered a question that was already
     * answered, differently.
     *
     * <p><b>Both orders, and this picks.</b> What a value is decoded on and what the number it
     * answers is measured on are two, and the one this wants is the first. Given the carrier instead
     * of the pair, every caller chose which end to hand over and every one of them had to choose the
     * same way — five places writing {@code .observed()} and getting it right, which is the
     * arrangement the whole of #1027 exists to stop. The decision is here, where the arms that need
     * it are.
     */
    static Reading at(TermOrders on, ObservedValue at) {
        NumericTerm.FromOnePosition term = on.term().atOnePosition();
        Carrier observed = on.observed();
        // A value or nothing at all, and nothing at all is not one of the answers here. Whether a
        // walk arrived and what it found are the caller's to have settled before a term is asked
        // for a number; answered with a reading, this would be where a place nobody looked at comes
        // back as a place holding no number, which is what having no value here means.
        Objects.requireNonNull(at, "a term is read at a value the walk came to");
        Membership.Incomplete unread = Membership.unread(at);
        if (unread != null) {
            return new Reading.Missing(unread.cause());
        }
        // A newtype is not a step in a path, so what sits at the position may be the construction and
        // the value one inside it. Asked again of what is inside rather than walked into: a limit
        // reached one layer down leaves a construction that reads perfectly well with nothing where
        // the value should be, and a walk that only looked at the outside would call that a value
        // this term does not hold.
        if (at instanceof ObservedValue.Constructed c && c.field("value") != null) {
            return at(on, c.field("value"));
        }
        return switch (term) {
            case NumericTerm.ValueOf _ -> asItStands(at, observed);
            case NumericTerm.TakenOf taken ->
                    taken(taken.takenAs(), taken.arguments(), taken.transformation(), at, on);
            case NumericTerm.CodePointClassCount count -> codePointsOfAClass(count.counted(), at);
        };
    }

    /**
     * The elements of one occurrence put together for a number of an element read off them
     * ({@link TermOrders#together}).
     */
    static <G> ElementsTogether<G> together(TermOrders on,
            List<Function<ElementProjection, Holding<G>>> each) {
        Objects.requireNonNull(each, "a term is read among the elements a walk came to");
        return switch (on.amongItsNeighbours()) {
            case NumericTerm.Multiplicity often -> new Counted<>(on.observed(), often.placeField(),
                    each);
            case NumericTerm.ExtremeOfItsKey _ -> new KeyedEnds<>(on, each);
        };
    }

    /**
     * How often each value the elements hold occurs among them.
     *
     * <p>Equal as the place's order has them: two values are one where the order puts them at one
     * place, which is how the language holds a decimal's amount and the value inside a newtype,
     * and so what a fold that files a counter under each key files them by. Read as the
     * observation's own equality, two decimals of one amount written to different scales would be
     * two values. A value the order puts nowhere, or one that was not read whole at any depth of
     * the newtypes around it, is not counted as the same or as another: no one number is read of
     * it, which is a reading that could not be made and not a statement that there is no number.
     * An element is one of the elements, so the number is at least one.
     *
     * <p>Every element's value is read, since any of them may be the element's equal. So what stops
     * an element is its own value where it holds nothing there, then the first element that holds
     * nothing, then its own value where that was not read, and then the first value in order that
     * was not.
     */
    private static final class Counted<G> implements ElementsTogether<G> {

        private final Carrier observed;
        private final ElementProjection field;
        /** Why the first element holding nothing at the field holds nothing, or null. */
        private final G firstNothing;
        /** Why the first value in order the order put nowhere is no number, or null. */
        private final Reading firstStop;
        /** How many values are at each place, by the place in its one representation. */
        private final Map<Place, Long> counted = new HashMap<>();

        Counted(Carrier observed, ElementProjection field,
                List<Function<ElementProjection, Holding<G>>> each) {
            this.observed = observed;
            this.field = field;
            G nothing = null;
            Reading stop = null;
            for (Function<ElementProjection, Holding<G>> one : each) {
                switch (one.apply(field)) {
                    case Holding.Nothing<G>(G why) -> nothing = nothing != null ? nothing : why;
                    case Holding.Value<G>(ObservedValue value) -> {
                        switch (whereTheOrderPuts(observed, value)) {
                            case Where.At(Place place) ->
                                    counted.merge(place.canonical(), 1L, Long::sum);
                            case Where.Nowhere nowhere ->
                                    stop = stop != null ? stop : nowhere.why();
                        }
                    }
                }
            }
            this.firstNothing = nothing;
            this.firstStop = stop;
        }

        @Override
        public Neighbouring<G> numberOf(
                Function<ElementProjection, Holding<G>> own) {
            return switch (own.apply(field)) {
                case Holding.Nothing<G>(G why) -> new Neighbouring.HeldNothing<>(why);
                case Holding.Value<G>(ObservedValue value) -> firstNothing != null
                        ? new Neighbouring.HeldNothing<>(firstNothing)
                        : new Neighbouring.Read<>(of(whereTheOrderPuts(observed, value)));
            };
        }

        private Reading of(Where own) {
            if (!(own instanceof Where.At(Place place))) {
                return ((Where.Nowhere) own).why();
            }
            return firstStop != null ? firstStop
                    : new Reading.Number(Count.of(counted.getOrDefault(place.canonical(), 0L)));
        }
    }

    /**
     * The least or the greatest of what the elements hold at the term's value, among those holding
     * at its key what the element holds there.
     *
     * <p>Alike as the key's order has them, as {@link Counted} counts them, and the values put on
     * the value's own order, which is the order the number is measured on. An element is one of
     * the elements, so some element is of its key and the number is one of the values.
     *
     * <p>Every key is read, since an element whose key is not read may be of any key and no end is
     * read beside it. A value is read only of an element of the key asked about, in order and only
     * until one of them is not read: what an element of another key holds, or failed to hold, is
     * no part of this key's end. So a key's values are read the first time an element of that key
     * is asked about and never for a key nobody asks about.
     *
     * <p>What stops an element is its own key where it holds nothing there, then the first element
     * in order that holds nothing at a key, or at a value of its key, whichever stands first; then
     * its own key where that was not read, and then whichever stands first of an element whose key
     * was not read and one of its key whose value was not.
     */
    private static final class KeyedEnds<G> implements ElementsTogether<G> {

        private final NumericTerm.ExtremeOfItsKey term;
        private final Carrier keyedOn;
        private final Carrier observed;
        private final List<Function<ElementProjection, Holding<G>>> each;
        /** Why the first element holding nothing at its key holds nothing, and where it is. */
        private G keyNothing;
        private int keyNothingAt = -1;
        /** Why the first key in order the key's order put nowhere is no number, and where. */
        private Reading keyStopped;
        private int keyStoppedAt = -1;
        /** Where each element of each key stands, by the key in its one representation. */
        private final Map<Place, List<Integer>> ofEachKey = new HashMap<>();
        /** What each key asked about came to. */
        private final Map<Place, OfAKey<G>> asked = new HashMap<>();

        KeyedEnds(TermOrders on, List<Function<ElementProjection, Holding<G>>> each) {
            if (!(on.amongItsNeighbours() instanceof NumericTerm.ExtremeOfItsKey keyed)) {
                throw new IllegalArgumentException(on.term() + " is the end of no key's values");
            }
            this.term = keyed;
            this.keyedOn = on.fieldCarrier(term.keyField());
            this.observed = on.observed();
            this.each = List.copyOf(each);
            for (int at = 0; at < this.each.size(); at++) {
                switch (this.each.get(at).apply(term.keyField())) {
                    case Holding.Nothing<G>(G why) -> {
                        if (keyNothing == null) {
                            keyNothing = why;
                            keyNothingAt = at;
                        }
                    }
                    case Holding.Value<G>(ObservedValue key) -> {
                        switch (whereTheOrderPuts(keyedOn, key)) {
                            case Where.At(Place place) -> ofEachKey.computeIfAbsent(
                                    place.canonical(), _ -> new ArrayList<>()).add(at);
                            case Where.Nowhere nowhere -> {
                                if (keyStopped == null) {
                                    keyStopped = nowhere.why();
                                    keyStoppedAt = at;
                                }
                            }
                        }
                    }
                }
            }
        }

        @Override
        public Neighbouring<G> numberOf(
                Function<ElementProjection, Holding<G>> own) {
            ObservedValue ownKey;
            switch (own.apply(term.keyField())) {
                case Holding.Nothing<G>(G why) -> {
                    return new Neighbouring.HeldNothing<>(why);
                }
                case Holding.Value<G>(ObservedValue value) -> ownKey = value;
            }
            Place itsKey;
            switch (whereTheOrderPuts(keyedOn, ownKey)) {
                case Where.Nowhere nowhere -> {
                    return keyNothing != null ? new Neighbouring.HeldNothing<>(keyNothing)
                            : new Neighbouring.Read<>(nowhere.why());
                }
                case Where.At(Place place) -> itsKey = place.canonical();
            }
            OfAKey<G> key = asked.computeIfAbsent(itsKey, this::read);
            if (keyNothing != null && (key.nothing() == null || keyNothingAt < key.stoppedAt())) {
                return new Neighbouring.HeldNothing<>(keyNothing);
            }
            if (key.nothing() != null) {
                return new Neighbouring.HeldNothing<>(key.nothing());
            }
            if (keyStopped != null && (key.stopped() == null || keyStoppedAt < key.stoppedAt())) {
                return new Neighbouring.Read<>(keyStopped);
            }
            if (key.stopped() != null) {
                return new Neighbouring.Read<>(key.stopped());
            }
            return new Neighbouring.Read<>(key.end() == null ? new Reading.NotNumber()
                    : new Reading.Number(key.end()));
        }

        /** The values of the elements of {@code key}, read in order until one is not. */
        private OfAKey<G> read(Place key) {
            Place end = null;
            for (int at : ofEachKey.getOrDefault(key, List.of())) {
                switch (each.get(at).apply(term.valueField())) {
                    case Holding.Nothing<G>(G why) -> {
                        return new OfAKey<>(end, why, null, at);
                    }
                    case Holding.Value<G>(ObservedValue value) -> {
                        switch (whereTheOrderPuts(observed, value)) {
                            case Where.At(Place held) -> end = end == null ? held
                                    : endOf(term.extreme(), end, held);
                            case Where.Nowhere nowhere -> {
                                return new OfAKey<>(end, null, nowhere.why(), at);
                            }
                        }
                    }
                }
            }
            return new OfAKey<>(end, null, null, -1);
        }
    }

    /**
     * What the values of one key came to, read in order until one was not.
     *
     * @param end       the end of the values read, or null where none was
     * @param nothing   why the value that stopped them holds nothing, or null
     * @param stopped   why the value that stopped them is no number, or null
     * @param stoppedAt where in order the value that stopped them stands, or -1 where none did
     */
    private record OfAKey<G>(Place end, G nothing, Reading stopped, int stoppedAt) {}

    /** The one of {@code kept} and {@code other} at {@code extreme}, the first where they are
     *  level. */
    private static Place endOf(Extreme extreme, Place kept, Place other) {
        return switch (extreme) {
            case Extreme.Least _ -> other.compareTo(kept) < 0 ? other : kept;
            case Extreme.Greatest _ -> other.compareTo(kept) > 0 ? other : kept;
        };
    }

    /** Where an order puts a value, or why it puts it nowhere. */
    private sealed interface Where {

        record At(Place place) implements Where {}

        record Nowhere(Reading why) implements Where {}
    }

    /**
     * Where {@code observed} puts {@code value}, read through each newtype around it as {@link
     * #at} reads one: whether what stands at each depth was read whole is asked again at that
     * depth, since a newtype that was read may hold a value that was not.
     */
    private static Where whereTheOrderPuts(Carrier observed, ObservedValue value) {
        ObservedValue at = value;
        while (true) {
            Membership.Incomplete unread = Membership.unread(at);
            if (unread != null) {
                return new Where.Nowhere(new Reading.Missing(unread.cause()));
            }
            if (at instanceof ObservedValue.Constructed c && c.field("value") != null) {
                at = c.field("value");
            } else {
                break;
            }
        }
        Place place = observed == null ? null : observed.placeOf(at);
        return place == null
                ? new Where.Nowhere(new Reading.Missing(
                        Incompleteness.Cause.of(Incompleteness.Code.VALUE_UNREADABLE)))
                : new Where.At(place);
    }

    /**
     * How many of the code points a string holds are in a class.
     *
     * <p>Counted in scalar values, as {@code String.length} counts, and against the one whitespace
     * alphabet the library's own operations scan with ({@link CodePointClass}). What is read is the
     * string as the row wrote it, so a count read here is the count the run time's own scan of that
     * string comes to.
     */
    private static Reading codePointsOfAClass(CodePointClass counted, ObservedValue at) {
        return at instanceof ObservedValue.Text text
                ? new Reading.Number(Count.of(text.value().codePoints()
                        .filter(counted::contains).count()))
                : new Reading.NotNumber();
    }

    /**
     * The number a term names over the values of its run, or why there is none.
     *
     * <p>Handed the values rather than reaching for them: which rows there are and how many values
     * stand at a place in one are the measure's, and a term only says what its number is of them.
     * The plural is the whole difference from a taking of one value, and it is here rather than in
     * the path or in what a row is asked — a location says nothing about how many values stand at
     * it, and a reader that asked for one where a run stands would be given the first of them or
     * none.
     *
     * <p>Exhaustive over the accounts, with no {@code default}. An account of a number taken of one
     * value says nothing about a run of them — which hour a run of times falls in is not a question
     * — so those answer that this is no number of theirs rather than being read as whichever value
     * came first.
     */
    static Reading over(TermOrders on, java.util.List<ObservedValue> values) {
        NumericTerm.TakenOver term = (NumericTerm.TakenOver) on.term();
        // The values of a run the walk came to, and every one of them a value. A run this compiler
        // could not reach has none of these and is not a run of none, so the caller settles that
        // before asking a term for a number -- given nothing here instead, a run nobody walked to
        // would come out as the model having written an empty one.
        Objects.requireNonNull(values, "a term is read over the values a walk came to");
        for (ObservedValue each : values) {
            Objects.requireNonNull(each, "every value of a run the walk came to is a value");
            Membership.Incomplete unread = Membership.unread(each);
            if (unread != null) {
                return new Reading.Missing(unread.cause());
            }
        }
        if (term.source() instanceof RunSource.ReachableNodes nodes) {
            List<ObservedValue> held = new ArrayList<>();
            Reading stopped = heldBelow(values, nodes, held);
            if (stopped != null) {
                return stopped;
            }
            values = held;
        }
        return switch (term.takenAs()) {
            case TakenAs.TheSumOfWhatItHolds _ -> addedUp(values, on);
            // Each value of the run is one of them, whatever it is.
            case TakenAs.HowManyItHolds _ -> new Reading.Number(Count.of(values.size()));
            case TakenAs.PartOfTime _, TakenAs.PartOfDate _,
                    TakenAs.TheTruncatingQuotient _, TakenAs.TheFloorRemainder _ ->
                    new Reading.NotNumber();
        };
    }

    /**
     * The values a tree holds below each of {@code roots}, put into {@code held}: every node from
     * the root down through the fields {@code nodes} names, or what the container it names holds
     * in each of them — or why a node has none, where it was not read or is no record holding
     * those fields as containers.
     */
    private static Reading heldBelow(List<ObservedValue> roots, RunSource.ReachableNodes nodes,
                                     List<ObservedValue> held) {
        Deque<ObservedValue> below = new ArrayDeque<>(roots);
        while (!below.isEmpty()) {
            ObservedValue node = below.removeFirst();
            Membership.Incomplete unread = Membership.unread(node);
            if (unread != null) {
                return new Reading.Missing(unread.cause());
            }
            if (nodes.container().isEmpty()) {
                held.add(node);
            } else {
                List<ObservedValue> inside = elementsAt(node, nodes.container());
                if (inside == null) {
                    return new Reading.NotNumber();
                }
                held.addAll(inside);
            }
            for (String field : nodes.through()) {
                List<ObservedValue> next = elementsAt(node, List.of(field));
                if (next == null) {
                    return new Reading.NotNumber();
                }
                below.addAll(next);
            }
        }
        return null;
    }

    /** The elements of the container at {@code fields} of {@code value}, or null where there is
     *  no container there. */
    private static List<ObservedValue> elementsAt(ObservedValue value, List<String> fields) {
        ObservedValue at = value;
        for (String field : fields) {
            if (!(at instanceof ObservedValue.Constructed record) || record.field(field) == null) {
                return null;
            }
            at = record.field(field);
        }
        return switch (at) {
            case ObservedValue.Sequence sequence -> sequence.elements();
            case null, default -> null;
        };
    }

    /**
     * The number a term names over what a walk computed of each element, or why there is none.
     *
     * <p>One reading per element, each answering what stands at a field of that element, because
     * the computation reads several of them and values gathered field by field would pair one
     * element's number with another's. What an element comes to is the computation's, applied to
     * the numbers its fields hold; what is added up is those, in the exact arithmetic.
     *
     * <p>An element whose computed number the carrier of what the walk answers cannot hold is one
     * the program stops at rather than one it answers, so the row has no number for the run. Read as
     * the exact sum it would be a total the program never returns.
     */
    static Reading overElements(TermOrders on,
                                List<Function<ElementProjection, ObservedValue>> each) {
        NumericTerm.TakenOver term = (NumericTerm.TakenOver) on.term();
        Objects.requireNonNull(each, "a term is read over the elements a walk came to");
        if (!(term.source() instanceof RunSource.ComputedOccurrences computed)
                || !(term.takenAs() instanceof TakenAs.TheSumOfWhatItHolds)) {
            return new Reading.NotNumber();
        }
        Carrier answeredPerElement = on.observed();
        if (answeredPerElement == null) {
            return new Reading.NotNumber();
        }
        List<ExactRatio> terms = new ArrayList<>();
        for (Function<ElementProjection, ObservedValue> element : each) {
            // The fields are asked for as the computation needs them, so what a row holds at a
            // field the element's own choice does not reach is no part of this element's number.
            OneElement fields = new OneElement(on, element);
            ExactAnswer<ExactRatio> made =
                    computed.computation().at(fields::number, fields::flag);
            if (made == null) {
                return fields.stopped != null ? fields.stopped : new Reading.NotNumber();
            }
            if (!(made instanceof ExactAnswer.Held<ExactRatio> exact)) {
                return new Reading.NotWorkedOut(
                        ((ExactAnswer.Unheld<ExactRatio>) made).why());
            }
            // The one the program computes, which is what the carrier of the answer holds.
            switch (exact.value().writtenDecimal()) {
                case ExactAnswer.Unheld<Optional<BigDecimal>> unheld -> {
                    return new Reading.NotWorkedOut(unheld.why());
                }
                case ExactAnswer.Held<Optional<BigDecimal>> written -> {
                    if (written.value().isEmpty()) {
                        return new Reading.NotWorkedOut(UnheldNumber.NO_REPRESENTATION_EXISTS);
                    }
                    if (answeredPerElement.onTheGrid(new Count(written.value().get())) == null) {
                        return new Reading.NotNumber();
                    }
                }
            }
            terms.add(exact.value());
        }
        return sumOf(terms);
    }

    /**
     * What one element holds at the fields a computation asks it for, and why it stopped where it
     * did.
     *
     * <p>A field answered as nothing records why no number came of it and says nothing to the
     * computation, which gives up on that element; the reading is then what was recorded and not a
     * guess at what a field with no value would have meant.
     */
    private static final class OneElement {

        private final TermOrders on;
        private final Function<ElementProjection, ObservedValue> element;
        private Reading stopped;

        OneElement(TermOrders on, Function<ElementProjection, ObservedValue> element) {
            this.on = on;
            this.element = element;
        }

        ExactRatio number(ElementProjection field) {
            ObservedValue at = held(field);
            Carrier carrier = at == null ? null : on.fieldCarrier(field);
            Place place = carrier == null ? null : carrier.placeOf(at);
            if (at != null && !(place instanceof Count)) {
                stopped = new Reading.NotNumber();
            }
            return place instanceof Count count ? count.exactly() : null;
        }

        Boolean flag(ElementProjection field) {
            ObservedValue at = held(field);
            if (at != null && !(at instanceof ObservedValue.Bool)) {
                stopped = new Reading.NotNumber();
            }
            return at instanceof ObservedValue.Bool set ? set.value() : null;
        }

        /** The value at the field, or null with the reason recorded where there is none to use. */
        private ObservedValue held(ElementProjection field) {
            ObservedValue at = element.apply(field);
            // A field the element holds no value at is an element this is no number of, as an
            // observation of the wrong shape is.
            if (at == null) {
                stopped = new Reading.NotNumber();
                return null;
            }
            Membership.Incomplete unread = Membership.unread(at);
            if (unread != null) {
                stopped = new Reading.Missing(unread.cause());
                return null;
            }
            return at;
        }
    }

    /** The number the term is, where the term is what the location holds. */
    private static Reading asItStands(ObservedValue at, Carrier observed) {
        if (observed == null) {
            return new Reading.NotNumber();
        }
        Place read = observed.placeOf(at);
        return read == null ? new Reading.NotNumber() : new Reading.Number(read);
    }

    /**
     * The number an operation answers of an observation of what it was given.
     *
     * <p>One arm per declared account of what such an operation takes, and no default. An account
     * added to {@code semantics} is one this does not compile without, which is what keeps a term
     * from being read as whichever arm was written first — the state {@code SizeOf} left the reader
     * in, where a term standing for anything but a size would have been read as the observation
     * itself (#1027).
     *
     * <p>The pair and not one end of it, because which end an account reads its values on is the
     * account's own answer. A part of a time is a number of the value as it is written; what a
     * container adds up to is a number of the values it holds, and those are places of the order the
     * total is measured on. Handed one carrier for every arm, the arms that want the other end have
     * nothing to say so with — and a container is written on no order at all, so the one that adds
     * its elements up is handed nothing.
     */
    private static Reading taken(TakenAs how, TakenArguments arguments, ValueTransformation from,
                                 ObservedValue at, TermOrders on) {
        return switch (how) {
            case TakenAs.HowManyItHolds _ -> howMany(at);
            case TakenAs.TheSumOfWhatItHolds _ -> addedUp(at, on);
            case TakenAs.PartOfTime taken -> partOfTime(taken.part(), at, on.observed());
            case TakenAs.PartOfDate taken -> partOfDate(taken.part(), from, at, on.observed());
            case TakenAs.TheTruncatingQuotient taken ->
                    quotient(taken.read(arguments), at, on.observed());
            case TakenAs.TheFloorRemainder taken ->
                    remainder(taken.read(arguments), at, on.observed());
        };
    }

    /**
     * The remainder of an observed value by the divisor the term carries, floored.
     *
     * <p>Divided the way the operation divides, so what is read off a row is the number that row's
     * run computes. Both ends are the order the value is written on, as a quotient's are. No divisor
     * is a term nothing built, and is answered as an observation of the wrong shape is.
     */
    private static Reading remainder(BigDecimal by, ObservedValue at, Carrier observed) {
        if (observed == null || by == null || by.signum() == 0) {
            return new Reading.NotNumber();
        }
        Place read = observed.placeOf(at);
        if (!(read instanceof Count count)) {
            return new Reading.NotNumber();
        }
        return switch (Arithmetic.AFloorRemainder.remainderOf(count.at(), by)) {
            case ExactAnswer.Unheld<BigDecimal> unheld -> new Reading.NotWorkedOut(unheld.why());
            case ExactAnswer.Held<BigDecimal> held -> {
                Place remainder = observed.onTheGrid(new Count(held.value()));
                yield remainder == null ? new Reading.NotNumber() : new Reading.Number(remainder);
            }
        };
    }

    /**
     * The whole-number quotient of an observed value by the divisor the term carries.
     *
     * <p>Divided the way the operator divides — toward zero — so what is read off a row is the
     * number that row's run computes and not a rounding of it. Both ends are the same order here: a
     * whole number and its quotient are counted by one, so the value is read and the answer given
     * on the order the position is written on.
     *
     * <p>No divisor is a term nothing built: a taking whose divisor reads as no constant, or as
     * nought, is refused where the term is made. Answered here as an observation of the wrong shape
     * is, so that a reader reaching it is told what it has rather than stopped.
     */
    private static Reading quotient(BigDecimal by, ObservedValue at, Carrier observed) {
        if (observed == null || by == null || by.signum() == 0) {
            return new Reading.NotNumber();
        }
        Place read = observed.placeOf(at);
        if (!(read instanceof Count count)) {
            return new Reading.NotNumber();
        }
        // A quotient past the end of what a whole number holds is one no run answers: the smallest
        // of them over minus one is a number the operator aborts at rather than a number a row has.
        // Asked of the carrier, which is where what a whole number stops at is answered.
        return switch (Arithmetic.ATruncatingQuotient.quotientOf(count.at(), by)) {
            case ExactAnswer.Unheld<BigDecimal> unheld -> new Reading.NotWorkedOut(unheld.why());
            case ExactAnswer.Held<BigDecimal> held -> {
                Place quotient = observed.onTheGrid(new Count(held.value()));
                yield quotient == null ? new Reading.NotNumber() : new Reading.Number(quotient);
            }
        };
    }

    /**
     * How much an observation holds.
     *
     * <p>Read off the observation under the premise {@link NumericTerm.TakenOf} states: the
     * operation and what it is applied to agree, so counting what is there counts what was asked
     * for. A string counts in scalar values, by the count the run time's {@code String.length}
     * answers with ({@link ScalarValues#count}).
     */
    private static Reading howMany(ObservedValue at) {
        return switch (at) {
            case ObservedValue.Text t -> new Reading.Number(Count.of(ScalarValues.count(t.value())));
            case ObservedValue.Sequence s -> new Reading.Number(Count.of(s.elements().size()));
            case ObservedValue.Mapping m -> new Reading.Number(Count.of(m.entries().size()));
            case null, default -> new Reading.NotNumber();
        };
    }

    /**
     * What an observed container's elements add up to.
     *
     * <p>Every element, on the order the answer is measured on. That order is the elements' own —
     * a walk carries what it has so far in the type it answers — so an element is read as a place
     * of the same carrier the sum is, and there is no second order here for the two ends of the
     * term to come apart on.
     *
     * <p>An element that reads as no place is what a container holding something other than what
     * the position declares would give, and the sum of those is not a number rather than a number
     * missing one of its parts. Nothing here reaches into an element: a sum is over what a
     * container holds, and a value inside one of them is a position of its own.
     *
     * <p>Nothing added up is nought, which is what the walk starts from. An empty container is a
     * value the model may write, and answering that it holds no number would put a row the author
     * can write outside every class of the number a rule is about.
     */
    private static Reading addedUp(ObservedValue at, TermOrders on) {
        return at instanceof ObservedValue.Sequence held
                ? addedUp(held.elements(), on) : new Reading.NotNumber();
    }

    /**
     * The same, over values a caller gathered rather than over a container standing somewhere.
     *
     * <p>Where the end is taken, for both readers at once. A total of what a place holds and a total
     * over the values of a run are one account of one operation, so which order their elements are
     * places of is one answer. Taken apiece, the two are free to add the same values up on different
     * orders.
     */
    private static Reading addedUp(java.util.List<ObservedValue> values, TermOrders on) {
        Carrier elements = on.answered();
        if (elements == null) {
            return new Reading.NotNumber();
        }
        List<ExactRatio> terms = new ArrayList<>();
        for (ObservedValue each : values) {
            Membership.Incomplete unread = Membership.unread(each);
            if (unread != null) {
                return new Reading.Missing(unread.cause());
            }
            // Through the name an element is written under, as the one value a place holds is read
            // through it. A run of a newtype over a whole number holds constructions, and the
            // number each carries is one inside.
            ObservedValue value = each instanceof ObservedValue.Constructed c
                    && c.field("value") != null ? c.field("value") : each;
            Place read = elements.placeOf(value);
            if (!(read instanceof Count count)) {
                return new Reading.NotNumber();
            }
            terms.add(count.exactly());
        }
        return sumOf(terms);
    }

    /**
     * What the numbers add up to, as the number a term answers.
     *
     * <p>One sum of them all, for both of the readers that gather numbers a run holds: the one that
     * reads a value at a place of each element and the one that computes one from several places of
     * it. The two are one account of one operation, so what a sum too wide for the exact arithmetic
     * comes to is one answer.
     */
    private static Reading sumOf(List<ExactRatio> terms) {
        // A container may hold a model's own decimals, spaced as widely apart in scale as any two
        // of them this compiler ever adds — the same hazard `check.ConstantAlgebra` guards against
        // when a rule adds two of them. The values are numbers and the sum is a number of them;
        // what a sum this wide meets is the exact arithmetic's own limit and not a question about
        // whether a term is one, so it is read as `NotWorkedOut` rather than let throw or folded
        // into a sentence that says the values are not numbers at all. One sum of them all, so
        // whether it is held does not turn on the order the container holds them in.
        ExactRatio total;
        switch (ExactRatio.sum(terms)) {
            case ExactAnswer.Held<ExactRatio> held -> total = held.value();
            case ExactAnswer.Unheld<ExactRatio> unheld -> {
                return new Reading.NotWorkedOut(unheld.why());
            }
        }
        return switch (total.writtenDecimal()) {
            case ExactAnswer.Unheld<Optional<BigDecimal>> unheld ->
                    new Reading.NotWorkedOut(unheld.why());
            case ExactAnswer.Held<Optional<BigDecimal>> held -> held.value().isEmpty()
                    ? new Reading.NotWorkedOut(UnheldNumber.NO_REPRESENTATION_EXISTS)
                    : new Reading.Number(new Count(held.value().get()));
        };
    }

    /**
     * Which hour, minute or second of its day an observed time falls in.
     *
     * <p>Decoded on the order the value is written on — a time counts the seconds into its day — and
     * answered on the order the operation answers, which is a count by one. The two are different
     * orders here, which is why the value is not read on the order the answer is measured on: read
     * that way, {@code 13:45:12} would be the thirteenth second rather than the thirteenth hour.
     *
     * <p>Divided and then taken the remainder of, which is what a part of a count is. The hour is
     * the whole hours in the day so far; the minute is the whole minutes, of which the hours are
     * dropped.
     */
    private static Reading partOfTime(TakenAs.TimePart part, ObservedValue at, Carrier observed) {
        if (observed == null) {
            return new Reading.NotNumber();
        }
        Place read = observed.placeOf(at);
        // A place that is not a count is not a time of day. No operation declaring this arm is
        // given anything else, so this is the observation being something other than what the
        // position declares, which is what `NotNumber` says.
        if (!(read instanceof Count count)) {
            return new Reading.NotNumber();
        }
        // Divided as numbers: which hour, minute or second a count of seconds falls in is a fact
        // about the number and not the places it came written to, and the whole number of this
        // part's seconds in it is one the exact arithmetic says it could not hold rather than
        // one a decimal division throws over.
        return switch (count.exactly().dividedBy(ExactRatio.of(part.seconds()))
                .flatMap(ExactRatio::truncated)) {
            case ExactAnswer.Unheld<BigInteger> unheld -> new Reading.NotWorkedOut(unheld.why());
            case ExactAnswer.Held<BigInteger> whole -> new Reading.Number(Count.of(new BigDecimal(
                    whole.value().remainder(BigInteger.valueOf(part.many())))));
        };
    }

    /**
     * Which year, month or day of its month an observed date falls in.
     *
     * <p>Turned into a date and asked, rather than divided. A date counts days and its parts are the
     * calendar's: the months are of different lengths and a leap year has a day the year before it
     * does not, so no step and modulus over the count answers any of the three. What turns a count
     * into a date is {@link Dates}, which is also what a report and a fixture read, so the date this
     * takes a part of is the date they would write for the same day.
     *
     * <p>Answered on the order the operation answers, which is a count by one, while the value is
     * decoded on the order it is written on. The two are the same pair of orders a part of a time
     * travels on, and for the same reason: a line at the twelfth month is not a line at the twelfth
     * day.
     */
    private static Reading partOfDate(TakenAs.DatePart part, ValueTransformation from,
                                      ObservedValue at, Carrier observed) {
        if (observed == null) {
            return new Reading.NotNumber();
        }
        Place read = observed.placeOf(at);
        // A place that is not a count is not a date. No operation declaring this arm is given
        // anything else, so this is the observation being something other than what the position
        // declares, which is what `NotNumber` says.
        if (!(read instanceof Count count) || observed.onTheGrid(count) == null) {
            return new Reading.NotNumber();
        }
        Count moved = from instanceof ValueTransformation.Identity ? count : movedBy(from, count);
        if (moved == null) {
            // The date is one the shifts that made the value this is taken of stop at: the program
            // aborts before there is a date to take a part of, as it does for a quotient past what
            // a whole number holds.
            return new Reading.NotWorkedOut(UnheldNumber.NO_REPRESENTATION_EXISTS);
        }
        java.time.LocalDate date = Dates.dateAt(moved);
        return new Reading.Number(Count.of(switch (part) {
            case YEAR -> date.getYear();
            case MONTH -> date.getMonthValue();
            case DAY -> date.getDayOfMonth();
        }));
    }

    /**
     * The day {@code day} becomes under {@code from}, or null where some step of it is not defined
     * there.
     *
     * <p>Null is the answer of the program the value was made by and not a gap in what is read: the
     * date is one it never gets past, so there is no date to take a part of.
     */
    private static Count movedBy(ValueTransformation from, Count day) {
        DateTranslation translation = from.translation();
        // A day of a date the carrier holds, which is a whole number inside the calendar's range,
        // so the whole number it truncates to is the day itself.
        if (!(day.exactly().truncated() instanceof ExactAnswer.Held<BigInteger> whole)) {
            return null;
        }
        long origin = whole.value().longValue();
        return translation.definedAt(origin) ? Count.of(origin + translation.offsetDays()) : null;
    }
}
