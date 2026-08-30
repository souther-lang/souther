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
 * <p><b>Two variants under one capability.</b> Both of the terms there are today are answered by a
 * single position of the input, and that is what {@link FromOnePosition} says — the capability a
 * reader needs before it may draw a line, classify what stands somewhere, or ask a search to write a
 * value. Whether such a number is what a location holds or what an operation answered of it is a
 * fact about the shape of the term. Which operation,
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
public sealed interface NumericTerm permits NumericTerm.FromOnePosition, NumericTerm.TakenOver {

    /**
     * A number a row can be asked for at one place, because one value stands there.
     *
     * <p>What separates these from a number read from somewhere else is not how many values the
     * operation looks at — a count reads every element of what it is given — but whether the term
     * is answered by one position of the input. That is the whole of what an axis, a threshold and
     * a search for a row need, and it is a capability rather than a shape: a reader that has one of
     * these may act on the position, and a reader holding a bare {@link NumericTerm} may not.
     */
    sealed interface FromOnePosition extends NumericTerm permits ValueOf, TakenOf {

        /**
         * The single input position this term is read from.
         *
         * <p>Not a claim that the number itself stands there. {@code Time.hour(slot.at)} is
         * answered from {@code slot.at} and no hour is written at it; what is written there is a
         * time. What the position gives is somewhere a row can be asked to hold a value, which is
         * what every reader of this method is doing with it.
         */
        TermPath position();

        @Override
        default TermPath subjectPath() {
            return position();
        }

        /** The number this term names at the one value standing at its position, or why there is
         *  none. */
        default Reading read(ObservedValue at, TermOrders on) {
            return NumericTerm.read(this, at, on);
        }
    }

    /** The number a location holds: a numeric parameter, a field of one, a numeric newtype's value. */
    record ValueOf(TermPath position) implements FromOnePosition {

        @Override
        public String toString() {
            return position.toString();
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
    final class TakenOf implements FromOnePosition {

        private final ValueName.Stdlib operation;
        private final TermPath position;

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
        private TakenOf(ValueName.Stdlib operation, TermPath position) {
            this.operation = java.util.Objects.requireNonNull(operation,
                    "a taken number is taken by an operation");
            this.position = java.util.Objects.requireNonNull(position, "and taken of somewhere");
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
        public static TakenOf of(ValueName.Stdlib operation, TermPath position, Type at,
                                 Symbols symbols) {
            TakenAs how = OperationFacts.takenAs(operation);
            // Of what stands here, because for an operation that walks a container the answer is
            // what the container holds. Asked of the operation alone, a sum answered no number this
            // could name and no term was made for any rule written on one.
            Type answers = NumericAnswers.typeOf(operation, at, symbols);
            if (how == null || answers == null || at == null) {
                return null;
            }
            return how.takenOf(souther.compiler.check.TypeOps.base(at, symbols), answers)
                    ? new TakenOf(operation, position) : null;
        }

        /** The operation whose answer this term is. */
        public ValueName.Stdlib operation() {
            return operation;
        }

        @Override
        public TermPath position() {
            return position;
        }

        /** What this operation takes of the value at {@link #position()}. Never null: one of these
         *  cannot be built for an operation that declares none. */
        public TakenAs takenAs() {
            return OperationFacts.takenAs(operation);
        }

        /** By the operation and the location, which is what makes two of these one term. */
        @Override
        public boolean equals(Object other) {
            return other instanceof TakenOf taken
                    && operation.equals(taken.operation) && position.equals(taken.position);
        }

        @Override
        public int hashCode() {
            return java.util.Objects.hash(operation, position);
        }

        @Override
        public String toString() {
            return operation.qualified() + "(" + position + ")";
        }
    }

    /**
     * A number an operation took over a run of values, which no single position answers.
     *
     * <p>The dual of {@link TakenOf} and named for it: one takes a number of the value at a place,
     * this takes one over the values a walk was given. What differs is not how many values the
     * operation looks at — a count of a container reads every element of it — but whether there is
     * one place a row can be asked to hold the value the number is taken of. A list an operation
     * built stands nowhere a row writes, so there is none, and a line drawn on this divides no
     * position.
     *
     * <p><b>Where the values came from is not where a line falls.</b> {@link #subjectPath} says
     * where to look and where to send a reader; it is not a position whose values a class could be
     * a class of. Two lines of sixty and forty are on the boundary of a hundred as surely as one of
     * a hundred is, so a class at the element position would be a class about a rule the model does
     * not state — which is why this term has no {@link FromOnePosition#position}, and every reader
     * that would draw one is a reader that cannot hold this.
     *
     * <p>Only for an operation that has declared how its number is taken, as a taking of one value
     * is. What the declaration settles is every other answer about the term, and the account is
     * applied to the values of the run rather than to a value standing at a place.
     */
    final class TakenOver implements NumericTerm {

        private final ValueName.Stdlib operation;
        private final RunSource source;

        private TakenOver(ValueName.Stdlib operation, RunSource source) {
            this.operation = operation;
            this.source = source;
        }

        /**
         * The term for what {@code operation} answers over the values at {@code source}, or null
         * where the two do not go together.
         *
         * <p><b>The one way one of these is made</b>, for the reason {@link TakenOf#of} is: the
         * account the operation declares is what settles every other answer about the term, so one
         * built without putting the two to that account would be read as whatever the reader's
         * default happened to be. What is asked is the same question, of a container of the values
         * the run holds — which is what the operation was given.
         *
         * @param each what stands at the place the run's values are read from
         */
        public static TakenOver of(ValueName.Stdlib operation, RunSource source, Type each,
                                   Symbols symbols) {
            TakenAs how = OperationFacts.takenAs(operation);
            // A container of what the run holds, with the names its values are written under taken
            // off — the same reach {@link TakenOf#of} takes of the value at a place, and for the
            // same reason: a name wrapped round a whole number is what the account is taken of.
            Type over = each == null ? null
                    : new Type.ListOf(souther.compiler.check.TypeOps.base(each, symbols));
            Type answers = over == null ? null
                    : NumericAnswers.typeOf(operation, over, symbols);
            if (how == null || answers == null || source == null) {
                return null;
            }
            return how.takenOf(over, answers) ? new TakenOver(operation, source) : null;
        }

        public ValueName.Stdlib operation() {
            return operation;
        }

        public RunSource source() {
            return source;
        }

        /** What this operation takes of what it is given. Never null: one of these cannot be made
         *  for an operation that declares none. */
        public TakenAs takenAs() {
            return OperationFacts.takenAs(operation);
        }

        /** By the operation and where its values come from, which is what makes two of these one
         *  term. */
        @Override
        public boolean equals(Object other) {
            return other instanceof TakenOver over
                    && operation.equals(over.operation) && source.equals(over.source);
        }

        @Override
        public int hashCode() {
            return java.util.Objects.hash(operation, source);
        }

        @Override
        public TermPath subjectPath() {
            return source.subjectPath();
        }

        /**
         * The number this term names over the values of its run, or why there is none.
         *
         * <p>Handed the values rather than reaching for them: which rows there are and how many
         * values stand at a place in one are the measure's, and a term only says what its number is
         * of them. The plural is the whole difference from a taking of one value, and it is here
         * rather than in the path or in what a row is asked — a location says nothing about how
         * many values stand at it, and a reader that asked for one where a run stands would be
         * given the first of them or none.
         *
         * <p>Exhaustive over the accounts, with no {@code default}. An account of a number taken of
         * one value says nothing about a run of them — which hour a run of times falls in is not a
         * question — so those answer that this is no number of theirs rather than being read as
         * whichever value came first.
         */
        public Reading readOver(java.util.List<ObservedValue> values, TermOrders on) {
            // Nothing to read, which a caller that could not walk to the run answers with. Said as
            // "this is no number of that" rather than as a total over the values it did find.
            if (values == null) {
                return new Reading.NotNumber();
            }
            for (ObservedValue each : values) {
                Membership.Incomplete unread = Membership.unread(each);
                if (unread != null) {
                    return new Reading.Missing(unread.code());
                }
            }
            return switch (takenAs()) {
                case TakenAs.TheSumOfWhatItHolds _ -> addedUp(values, on);
                case TakenAs.HowManyItHolds _, TakenAs.PartOfTime _, TakenAs.PartOfDate _ ->
                        new Reading.NotNumber();
            };
        }

        @Override
        public String toString() {
            return operation.qualified() + "(" + source + ")";
        }
    }

    /**
     * Where the subject of this number is read or reported from.
     *
     * <p>Not a position at which this term may be divided. What a reader may do with this is go and
     * look — read the values, ask what the declarations put there, send an author to it — and none
     * of those is drawing a line. A term whose values come from a run of a sequence answers here as
     * readily as one answered by a single place, and only the second of them has a position a class
     * can be a class of ({@link FromOnePosition#position}).
     *
     * <p>Never the identity of the term either: two terms can be read from one location, and
     * reading one as the other is what this type exists to stop.
     */
    TermPath subjectPath();

    /**
     * This number where one input position answers it, or null where no single place does.
     *
     * <p>The one place the capability is asked. Every reader that goes on to draw a line, classify
     * what stands somewhere or ask a search for a value needs it, and each of them working it out
     * from what kind of term it is holding is as many readings of one question as there are
     * readers — of which the day a term of a new kind arrives, some would say yes.
     *
     * <p>Exhaustive over the terms there are, with no {@code default}. A kind added is one this
     * question is answered for rather than one that falls to whichever side the last reader's
     * condition happened to leave it on.
     */
    default FromOnePosition atOnePosition() {
        return switch (this) {
            case FromOnePosition at -> at;
            // A run of values is answered by no single place, which is the whole of what this term
            // is. Every reader that goes on to draw a line or ask for a value gets the answer here.
            case TakenOver _ -> null;
        };
    }

    /**
     * The same number, of what stands at {@code other} — or null where this operation and what
     * stands there do not go together.
     *
     * <p>For a name that stands at more than one position. A field every case of a sum spreads is
     * one field written once, so a line drawn on a number of it is one line, and it falls on that
     * number under each case; what moves is where the number is taken, and the operation is what it
     * was.
     *
     * <p>Put to the same predicate the term was built under and not moved on the caller's word.
     * Nothing about the two positions being one field is checked here, so what would otherwise
     * arrive is a term whose account of what it takes was written for a shape the new location does
     * not have.
     *
     * @param at what stands at {@code other}, as the signature wrote it
     */
    default NumericTerm movedTo(TermPath other, Type at, Symbols symbols) {
        return switch (this) {
            case ValueOf _ -> new ValueOf(other);
            case TakenOf taken -> TakenOf.of(taken.operation(), other, at, symbols);
            // What moves here is where a number is taken, and a run is not taken anywhere: its
            // values come from a place inside a sequence, and the name that would move is the
            // container's. Answered as "not there" rather than by rebuilding the run at a
            // location, which would be this reading inventing where a walk got its values.
            case TakenOver _ -> null;
        };
    }

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
                Type answers = NumericAnswers.typeOf(taken.operation(), positionType, symbols);
                yield answers == null ? null : Carrier.ofValue(answers, symbols);
            }
            // Asked of the operation as a taking is, and asked of what it was given: a run is a
            // container of the values standing at the place it is read from, so what the operation
            // answers of one is what it answers of a container of them. Written out here as the
            // element's own order instead, this would be the account of a walk that adds restated
            // for every account, and the first one that answers something else would be read as
            // answering what its elements are.
            case TakenOver over -> {
                Type answers = positionType == null ? null : NumericAnswers.typeOf(
                        over.operation(), new Type.ListOf(positionType), symbols);
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
            case TakenOf _, TakenOver _ ->
                    new TermOrders(observed, answeredOn(positionType, symbols));
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
    static Reading read(FromOnePosition term, ObservedValue at, TermOrders on) {
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
            return read(term, c.field("value"), on);
        }
        return switch (term) {
            case ValueOf _ -> asItStands(at, observed);
            case TakenOf taken -> taken(taken.takenAs(), at, on);
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
            // Asked of the operation, as a taking is. That a total of non-negative amounts is
            // itself non-negative is not among the answers: it follows from what the elements are
            // bounded by and from how many there may be, which is a statement about the run and
            // not about the operation. Declared here as a range of the operation, it would be
            // wrong for a run whose elements may be negative.
            case TakenOver over -> ResultRange.of(over.operation(), ConstantArguments.NONE);
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
