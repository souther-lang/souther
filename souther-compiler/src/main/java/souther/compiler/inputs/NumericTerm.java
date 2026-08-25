package souther.compiler.inputs;

import souther.compiler.check.Carrier;
import souther.compiler.check.NumericAnswers;
import souther.compiler.check.Symbols;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Dates;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.ObservedValue;
import souther.compiler.semantics.ConstantArguments;
import souther.compiler.semantics.OperationFacts;
import souther.compiler.semantics.ResultRange;
import souther.compiler.semantics.TakenAs;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

/**
 * The number a rule compares, and where that number is read from.
 *
 * <p>Not the position. A boundary is drawn on a number, and the number a rule names is sometimes the
 * content of a location and sometimes something taken of it — the length of a string, the size of a
 * container, which hour of its day a time falls in. The two were one thing here, so a position holding
 * a string was a position holding no number, and every rule written about its length came back as a
 * rule the model had not written. The discharge procedure has always kept them apart (spec
 * §invariant-discharge-terms); this is the same separation on the side that measures.
 *
 * <p><b>Two variants, and they are the only two there are.</b> Whether the number is what a location
 * holds or what an operation answered of it is a fact about the shape of the term. Which operation,
 * and therefore what its answer is measured by, where it runs, how it is read off a row and what
 * values answer a given number, are facts about the operation and are declared where those are
 * ({@code semantics.OperationFacts}). A variant per operation would put each of those answers back
 * inside the kind of term, which is what {@code SizeOf} was: a size is never negative was written
 * here, and the same proposition about {@code Int.abs} — declared in {@code semantics} — could not
 * be reached from a term at all (#1016, #1027).
 *
 * <p>So nothing below asks which operation it is holding. Every question a reader asks of a term is
 * either answered from the variant, where the variant is genuinely what settles it, or handed to the
 * operation. An operation added to the language is read by everything here without a line being
 * written for it.
 */
public sealed interface NumericTerm permits NumericTerm.ValueOf, NumericTerm.TakenOf {

    /** The number a location holds: a numeric parameter, a field of one, a numeric newtype's value. */
    record ValueOf(TermPath path) implements NumericTerm {

        @Override
        public String toString() {
            return path.toString();
        }
    }

    /**
     * A number taken of what a location holds: how long a string is, how many a container holds,
     * which hour of its day a time falls in.
     *
     * <p><b>Which operations those are is not written here.</b> They are the ones that declare an
     * account of what they take ({@code semantics.OperationFacts}), and a list of them on this side
     * would be a second list — right on the day it was written and wrong the day the declarations
     * moved, with nothing failing in between. This side names the question; that side is the list.
     * A description that named the operations went stale inside one change (#1027).
     *
     * <p>Keyed by the operation the call resolved to rather than by how it was written, so a term
     * here and an atom in the discharge procedure are the same term when they are the same operation
     * over the same location.
     *
     * <p><b>Only for an operation that has declared how its number is taken.</b> Checked here and
     * not at whichever factory happened to be reached: a record is constructible by anyone who can
     * name it, so a rule kept at the call sites is a rule until the next call site. What the
     * declaration settles is every other answer about the term, so a term without one is a term that
     * would be read as whatever the reader's default happened to be — which for a carrier is an end
     * moved onto a value the term never takes, and for a reading is a row classified against a
     * number the model never named, with nothing about either looking like a failure (#1027).
     *
     * <p><b>The operation and the location go together, and {@link #of} is what says so.</b> That
     * was a premise the two call sites carried between them, which is a claim about who builds one
     * today rather than a property of the term. Held at the way in, a term whose operation is not
     * what the location's shape is measured by cannot be made at all.
     *
     * <p>Not against the observed value, which would tell a string from a collection and leave the
     * one pair a reader might confuse undistinguished: a {@code List} and a {@code Set} are one
     * observation, and which of the two it was is the declared type's to say. So it is the declared
     * type that is asked, and {@link #read} applies the account to the observation without asking
     * again.
     */
    final class TakenOf implements NumericTerm {

        private final ValueName.Stdlib operation;
        private final TermPath path;

        /**
         * Built only where the operation and what stands at the location have been put to the one
         * predicate that says whether they go together.
         *
         * <p>Private, so {@link #of} is the way in and not merely the way in from outside this
         * package. A record's canonical constructor promises that any combination of its components
         * is a value, and these two are not: an account of what is taken is written for a shape, and
         * an operation over a shape the location does not have is a term whose reading would apply
         * that account to whatever happened to be there.
         *
         * <p>Package-private was the same premise a boundary further out — true of whoever writes in
         * this package rather than of the term — and this package's own tests were already going
         * round it (#1027).
         */
        private TakenOf(ValueName.Stdlib operation, TermPath path) {
            this.operation = java.util.Objects.requireNonNull(operation,
                    "a taken number is taken by an operation");
            this.path = java.util.Objects.requireNonNull(path, "and taken of somewhere");
        }

        /**
         * The term for what {@code operation} answers of what stands at {@code path}, or null where
         * the two do not go together.
         *
         * <p><b>The one way one of these is made.</b> Three things have to hold and each of them is
         * a proposition somebody already owns: the operation declares an account of what it takes
         * ({@code semantics.OperationFacts}), it answers a number ({@link NumericAnswers}), and what
         * stands at the location is what that account is taken of ({@link TakenAs#takenOf}). The
         * third was a premise the call sites carried — "the operation and the location agree, by
         * construction" — which is a claim about who happens to build one today and not an invariant
         * (#1027).
         *
         * <p>Null and not a refusal. Whether a call names a number the model has a term for is a
         * question every reader of an expression asks, and the answer "it does not" is one they all
         * have somewhere to put: no line is drawn and the rule is reported as one nothing read.
         *
         * <p>Asked of what the names wrap, since a name around a list is still a list — the same
         * reach {@link Carrier#ofValue} takes, and taken here so that no caller takes it itself.
         */
        public static TakenOf of(ValueName.Stdlib operation, TermPath path, Type at,
                                 Symbols symbols) {
            TakenAs how = OperationFacts.takenAs(operation);
            Type answers = NumericAnswers.typeOf(operation, symbols);
            if (how == null || answers == null || at == null) {
                return null;
            }
            return how.takenOf(souther.compiler.check.TypeOps.base(at, symbols), answers)
                    ? new TakenOf(operation, path) : null;
        }

        /** The operation whose answer this term is. */
        public ValueName.Stdlib operation() {
            return operation;
        }

        @Override
        public TermPath path() {
            return path;
        }

        /** What this operation takes of the value at {@link #path()}. Never null: one of these
         *  cannot be built for an operation that declares none. */
        public TakenAs takenAs() {
            return OperationFacts.takenAs(operation);
        }

        /** By the operation and the location, which is what makes two of these one term. */
        @Override
        public boolean equals(Object other) {
            return other instanceof TakenOf taken
                    && operation.equals(taken.operation) && path.equals(taken.path);
        }

        @Override
        public int hashCode() {
            return java.util.Objects.hash(operation, path);
        }

        @Override
        public String toString() {
            return operation.qualified() + "(" + path + ")";
        }
    }

    /** Where the value this is taken of sits. Never the identity of the term: two terms can be taken
     * of one location, and reading one as the other is what this type exists to stop. */
    TermPath path();

    /**
     * The order the number this term names is measured on, or null where it has none.
     *
     * <p>What a rule about the length of a string is counted as is an {@code Int} at a position no
     * line is drawn on, and what a rule about {@code Time.hour(t)} is counted as is a count by one at
     * a position counting the seconds of its day. Both follow from what the operation answers and
     * from nothing about where it was applied — asked of the position, the step of the answer was
     * the step of the argument, and the twelfth hour was a line at the twelfth second.
     *
     * <p>Which is why {@code positionType} may be absent. A caller reading a term under more steps
     * than the walk that finds an input's positions goes down has no position to ask, and what an
     * operation answers is what it answers all the same — asked for the type first, a caller would
     * either have nothing to pass or would write out the rule above a second time, at whichever call
     * site noticed. What is null there is a term measured by its own values, which is the one case
     * the position was the answer to.
     */
    default Carrier answeredOn(Type positionType, Symbols symbols) {
        return switch (this) {
            case ValueOf _ -> positionType == null ? null : Carrier.ofValue(positionType, symbols);
            case TakenOf taken -> {
                Type answers = NumericAnswers.typeOf(taken.operation(), symbols);
                yield answers == null ? null : Carrier.ofValue(answers, symbols);
            }
        };
    }

    /**
     * The order a value at {@link #path()} is decoded on, or null where nothing orders it.
     *
     * <p>The other end of the same term, and null for more than one reason. A container is not
     * ordered and is read by what it holds rather than by a count of its own; a position whose type
     * nothing here can follow has no order either. Both are answers a reader can act on — what is
     * refused is silently reading the value on the order its answer is measured on, which is right
     * for every operation whose two ends agree and wrong without a word for the first that does not.
     */
    default Carrier observedOn(Type positionType, Symbols symbols) {
        return positionType == null ? null : Carrier.ofValue(positionType, symbols);
    }

    /** Both ends together, which is what every reader of a row wants and what neither end alone is
     *  safe to stand in for. A term that is what a location holds has one order twice, and says so
     *  here rather than by two readings that happen to agree. */
    default TermOrders ordersAt(Type positionType, Symbols symbols) {
        Carrier observed = observedOn(positionType, symbols);
        return switch (this) {
            case ValueOf _ -> TermOrders.itself(observed);
            case TakenOf _ -> new TermOrders(observed, answeredOn(positionType, symbols));
        };
    }

    /**
     * The number this term names at an observation of {@link #path()}, or why there is none.
     *
     * <p>The one reader. What a class asks of a row, what a boundary asks of it, and what a report
     * prints were three walks down a value that agreed only because they were written the same way.
     *
     * <p>The orders are handed in rather than guessed at from the observation. A written temporal
     * says nothing about whether the position counts days or seconds — the declared type says it —
     * and a reader that sniffed the text for a {@code T} answered a question that was already
     * answered, differently.
     *
     * <p><b>Both of them, and this picks.</b> What a value is decoded on and what the number it
     * answers is measured on are two orders, and the one this wants is the first. Given the carrier
     * instead of the pair, every caller chose which end to hand over and every one of them had to
     * choose the same way — five places writing {@code .observed()} and getting it right, which is
     * the arrangement the whole of #1027 exists to stop, one layer along. The decision is here,
     * where the arms that need it are.
     */
    default Reading read(ObservedValue at, TermOrders on) {
        Carrier observed = on.observed();
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
            return read(c.field("value"), on);
        }
        return switch (this) {
            case ValueOf _ -> asItStands(at, observed);
            case TakenOf taken -> taken(taken.takenAs(), at, observed);
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
     */
    private static Reading taken(TakenAs how, ObservedValue at, Carrier observed) {
        return switch (how) {
            case TakenAs.HowManyItHolds _ -> howMany(at);
            case TakenAs.PartOfTime taken -> partOfTime(taken.part(), at, observed);
            case TakenAs.PartOfDate taken -> partOfDate(taken.part(), at, observed);
        };
    }

    /**
     * How much an observation holds.
     *
     * <p>Read off the observation under the premise {@link TakenOf} states: the operation and what it
     * is applied to agree, so counting what is there counts what was asked for. A string counts in
     * code points, as {@code Strings.length} does — counting UTF-16 units here would put a boundary
     * one place away from the rule that drew it for every string outside the basic plane.
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

    /** How the values beside a boundary on this term are found, which is what the number it names
     *  is measured on and never what stands at the position it was taken of. */
    default BoundaryDomain intervals(Type positionType, Symbols symbols) {
        return BoundaryDomain.on(answeredOn(positionType, symbols));
    }

    /**
     * What this term's values are, before any rule is read.
     *
     * <p>Open where the term is a location's own content: what an {@code Int} holds is what its type
     * holds, and a position nobody bounded is one the model draws no line through (ADR-0090). A term
     * that is what an operation answered is not that — a size is never negative, which is what keeps
     * a guard at zero from asking for a row one below it (spec §invariant-discharge-terms).
     *
     * <p><b>Asked of the operation, not answered here.</b> That a size is at or above nought is one
     * proposition with {@code Int.abs(x) >= 0}, and both are declared where what is true of the
     * language's operations is declared. Written out here instead, it was the same sentence in a
     * second vocabulary, and the half declared in {@code semantics} could not be reached from a term
     * (#1016). Nor is it read off what the operation takes: every operation sharing an account of
     * what it takes would carry one bound, which is the same defect one level along.
     *
     * <p>Read with nothing said about the arguments, because a term of this kind carries none: what
     * a size is taken of is a container and what a magnitude is taken of is the one number, and a
     * bound may only name an argument that is a number ({@code check.DischargeRules.holdBound}), so
     * an operation like these declares no row that names one. A term whose operation does take
     * numbers would have to answer them here rather than be read the same way and quietly come back
     * wider.
     */
    default NumericDomain.Bounds intrinsicBounds() {
        return switch (this) {
            case ValueOf _ -> NumericDomain.Bounds.OPEN;
            case TakenOf taken -> ResultRange.of(taken.operation(), ConstantArguments.NONE);
        };
    }

    /** The count at a value, keeping why there is none where there is none. */
    sealed interface Reading {

        record Number(Place value) implements Reading {}

        /** There was no value to read, and this is what stopped there being one. */
        record Missing(Incompleteness.Code code) implements Reading {}

        /** The value was read and this term is not a number of it. An answer about the value and not
         * about the observation: a {@code Text} where a number was expected is a class nothing holds,
         * and calling it unreadable would report a partition that does not fit its position as a row
         * nobody could read. */
        record NotNumber() implements Reading {}
    }
}
