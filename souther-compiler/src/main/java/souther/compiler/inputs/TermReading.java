package souther.compiler.inputs;

import souther.compiler.check.Carrier;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Dates;
import souther.compiler.numeric.Place;
import souther.compiler.observe.ObservedValue;
import souther.compiler.semantics.TakenAs;

import souther.compiler.inputs.NumericTerm.Reading;

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
        // Nothing arrived, which is the walk saying it has no value here rather than an observation
        // saying it could not keep one. Named apart, because the reader that words an observation's
        // code says what an observation did — and here there was none.
        if (at == null) {
            return new Reading.NoValue();
        }
        Membership.Incomplete unread = Membership.unread(at);
        if (unread != null) {
            return new Reading.Missing(unread.code());
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
            case NumericTerm.TakenOf taken -> taken(taken.takenAs(), at, on);
        };
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
        // Nothing to read, which a caller that could not walk to the run answers with. Said as
        // "this is no number of that" rather than as a total over the values it did find.
        if (values == null) {
            return new Reading.NotNumber();
        }
        for (ObservedValue each : values) {
            // An element the walk arrived at nothing for, which is not an observation of one. Said
            // apart for the reason the one value a place holds is, since a total over a run is over
            // whatever the run holds and one of them being nothing is not a limit having fired.
            if (each == null) {
                return new Reading.NoValue();
            }
            Membership.Incomplete unread = Membership.unread(each);
            if (unread != null) {
                return new Reading.Missing(unread.code());
            }
        }
        return switch (term.takenAs()) {
            case TakenAs.TheSumOfWhatItHolds _ -> addedUp(values, on);
            case TakenAs.HowManyItHolds _, TakenAs.PartOfTime _, TakenAs.PartOfDate _ ->
                    new Reading.NotNumber();
        };
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
    private static Reading taken(TakenAs how, ObservedValue at, TermOrders on) {
        return switch (how) {
            case TakenAs.HowManyItHolds _ -> howMany(at);
            case TakenAs.TheSumOfWhatItHolds _ -> addedUp(at, on);
            case TakenAs.PartOfTime taken -> partOfTime(taken.part(), at, on.observed());
            case TakenAs.PartOfDate taken -> partOfDate(taken.part(), at, on.observed());
        };
    }

    /**
     * How much an observation holds.
     *
     * <p>Read off the observation under the premise {@link NumericTerm.TakenOf} states: the
     * operation and what it is applied to agree, so counting what is there counts what was asked
     * for. A string counts in code points, as {@code Strings.length} does — counting UTF-16 units
     * here would put a boundary one place away from the rule that drew it for every string outside
     * the basic plane.
     */
    private static Reading howMany(ObservedValue at) {
        return switch (at) {
            case ObservedValue.Text t -> new Reading.Number(
                    Count.of(t.value().codePointCount(0, t.value().length())));
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
        java.math.BigDecimal total = java.math.BigDecimal.ZERO;
        for (ObservedValue each : values) {
            if (each == null) {
                return new Reading.NoValue();
            }
            Membership.Incomplete unread = Membership.unread(each);
            if (unread != null) {
                return new Reading.Missing(unread.code());
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
            total = total.add(count.at());
        }
        return new Reading.Number(new Count(total));
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
        java.math.BigDecimal seconds = count.at();
        return new Reading.Number(Count.of(seconds
                .divideToIntegralValue(java.math.BigDecimal.valueOf(part.seconds()))
                .remainder(java.math.BigDecimal.valueOf(part.many()))));
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
    private static Reading partOfDate(TakenAs.DatePart part, ObservedValue at, Carrier observed) {
        if (observed == null) {
            return new Reading.NotNumber();
        }
        Place read = observed.placeOf(at);
        // A place that is not a count is not a date. No operation declaring this arm is given
        // anything else, so this is the observation being something other than what the position
        // declares, which is what `NotNumber` says.
        if (!(read instanceof Count count)) {
            return new Reading.NotNumber();
        }
        java.time.LocalDate date = Dates.dateAt(count);
        return new Reading.Number(Count.of(switch (part) {
            case YEAR -> date.getYear();
            case MONTH -> date.getMonthValue();
            case DAY -> date.getDayOfMonth();
        }));
    }
}
