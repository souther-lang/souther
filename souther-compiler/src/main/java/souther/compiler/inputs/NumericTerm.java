package souther.compiler.inputs;

import souther.compiler.check.BoundOperationFacts;
import souther.compiler.check.Carrier;
import souther.compiler.check.NewtypeInners;
import souther.compiler.check.DeclarationAccess;
import souther.compiler.check.DefaultBoundOperationFacts;
import souther.compiler.check.Extreme;
import souther.compiler.check.NumberAt;
import souther.compiler.check.NumericAnswers;
import souther.compiler.check.NumericMeasures;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeOps;
import souther.compiler.numeric.CanonicalOrder;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.UnheldNumber;
import souther.compiler.numeric.ValueTransformation;
import souther.compiler.observe.Incompleteness;
import souther.compiler.partition.KeptOccurrences;
import souther.compiler.semantics.CaseMapping;
import souther.compiler.semantics.CodePointClass;
import souther.compiler.semantics.ConstantArguments;
import souther.compiler.semantics.ResultRange;
import souther.compiler.semantics.TakenArguments;
import souther.compiler.semantics.TakenAs;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;

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
public sealed interface NumericTerm
        permits NumericTerm.FromOnePosition, NumericTerm.TakenOver,
                NumericTerm.OfAnElementsNeighbours, NumericTerm.OccurrencesOfItsValue,
                NumericTerm.OccurrencesOfAKey, NumericTerm.GatheredUnderItsKey,
                NumericTerm.GatheredUnderAKey, NumericTerm.ProductOf {

    /**
     * One order over these, for a walk that has to take them in one: by what each is written as,
     * which is as much as a reader outside the region can say of one. Two written alike and not
     * one number are refused where they are walked ({@link CanonicalOrder#walking}), as
     * {@link InputAtom#inOneOrder} refuses them.
     */
    static CanonicalOrder<NumericTerm> inOneOrder() {
        return Comparator.<NumericTerm, String>comparing(String::valueOf)::compare;
    }

    /**
     * A number of an element read off the elements beside it in its container: how often its value
     * occurs, the end of its key's values.
     *
     * <p>One kind and not two terms each asked about separately, because what follows from being one
     * is the same for both: the number is read among the elements of the one occurrence of
     * {@link #container()} the element is in, the elements are looked at only at
     * {@link #fieldsRead()}, and nothing about it is read off one position. A reader asks it of
     * this type rather than of the two, so a third number of the kind is one that reader already
     * handles.
     */
    sealed interface OfAnElementsNeighbours extends NumericTerm
            permits Multiplicity, ExtremeOfItsKey {

        /** The container among whose elements the number is read. */
        TermPath container();

        /** The ways from an element of {@link #container()} to every value its number is read
         *  from, each of which an element of the shape the walk says holds. */
        List<ElementProjection> fieldsRead();
    }

    /**
     * A number a row can be asked for at one place, because one value stands there.
     *
     * <p>What separates these from a number read from somewhere else is not how many values the
     * operation looks at — a count reads every element of what it is given — but whether the term
     * is answered by one position of the input. That is the whole of what an axis, a threshold and
     * a search for a row need, and it is a capability rather than a shape: a reader that has one of
     * these may act on the position, and a reader holding a bare {@link NumericTerm} may not.
     */
    sealed interface FromOnePosition extends NumericTerm
            permits ValueOf, TakenOf, CodePointClassCount, CodePointValueSum, CodePointAt,
                    WholeUnitsOf {

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

        /** The same number, of the one value standing where {@code moved} puts {@link
         *  #position()}: never null, since one place moved is one place. */
        @Override
        FromOnePosition movedTo(PlacesMoved moved);
    }

    /** The number a location holds: a numeric parameter, a field of one, a numeric newtype's value. */
    record ValueOf(TermPath position) implements FromOnePosition {

        @Override
        public ValueOf movedTo(PlacesMoved moved) {
            return new ValueOf(moved.put(position));
        }

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
     * <p><b>And by what the operation was given beside the location.</b> A taking may be handed
     * values that decide which number it takes — a divisor is one — and two takings differing only
     * there are two numbers of one place: {@code x / 2} and {@code x / 3} are no more one term than
     * the length of a string and the hour of a time are. What those arguments read as is what is
     * carried, so a constant written out and a name given one are one term.
     *
     * <p><b>Only where there is an account of how its number is taken.</b> Checked here and not at
     * whichever factory happened to be reached: a record is constructible by anyone who can name
     * it, so a rule kept at the call sites is a rule until the next call site. What the account
     * settles is every other answer about the term, so a term without one is a term that would be
     * read as whatever the reader's default happened to be — which for a carrier is an end moved
     * onto a value the term never takes, and for a reading is a row classified against a number the
     * model never named, with nothing about either looking like a failure (#1027).
     *
     * <p>Declared of the operation, or derived for this call from a representation the operation
     * already has. A length is the first: what {@code String.length} takes is declared of it and is
     * the account of every call there is. A quotient is the second: what {@code Int.truncatingDivide}
     * computes is the arithmetic, and a call of it whose divisor the reading has as a number is a
     * number taken of what it divides, while the calls beside it are not. Which of the two it is
     * does not reach this far — the account is asked for with the arguments in hand
     * ({@code check.BoundOperationFacts}) and what comes back is the account or nothing.
     *
     * <p><b>The operation and the location go together, and {@link #of} is what says so.</b> That
     * was a premise the two call sites carried between them, which is a claim about who builds one
     * today rather than a property of the term. Held at the way in, a term whose operation is not
     * what the location's shape is measured by cannot be made at all.
     *
     * <p>Not against the observed value, which would tell a string from a collection and leave the
     * one pair a reader might confuse undistinguished: a {@code List} and a {@code Set} are one
     * observation, and which of the two it was is the declared type's to say. So it is the declared
     * type that is asked, and the reading applies the account to the observation without asking
     * again.
     */
    final class TakenOf implements FromOnePosition {

        private final ValueName.Stdlib operation;
        private final ObservationSource source;
        private final TakenArguments arguments;

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
        private TakenOf(ValueName.Stdlib operation, ObservationSource source,
                        TakenArguments arguments) {
            this.operation = java.util.Objects.requireNonNull(operation,
                    "a taken number is taken by an operation");
            this.source = java.util.Objects.requireNonNull(source, "and taken of somewhere");
            this.arguments = java.util.Objects.requireNonNull(arguments,
                    "and with whatever it was given beside that value, which is nothing where it"
                            + " was given nothing");
        }

        /**
         * The term for how many the value at {@code position} holds, taken by {@code operation} —
         * or null where the operation takes no such number of it.
         *
         * <p>The one way a container's size is named as a term. A rule counting it names the
         * operation, and a reader with only the type takes the one that counts what the type holds
         * ({@link NumericMeasures#takenOf}); both come to the same term for
         * a container, and a reader building it apart could hold one that answers something else.
         */
        public static TakenOf howManyHeldAt(ValueName.Stdlib operation, TermPath position,
                                            Type at, NewtypeInners inners, Symbols symbols) {
            TakenOf term = asItStands(operation, position, at, inners, symbols);
            return term != null && term.takenAs() instanceof TakenAs.HowManyItHolds ? term : null;
        }

        /**
         * The term for what {@code operation} answers of the value at {@code position} as it
         * stands, given nothing beside it, or null where the two do not go together.
         *
         * <p>Named for what it says of the value: the one the operation takes its number of is the
         * one at the position and nothing made of it. A caller that has what the value was made
         * into takes {@link #of} and says so, and cannot hand over the position alone and be read
         * as taking the number of it as it stands.
         */
        public static TakenOf asItStands(ValueName.Stdlib operation, TermPath position, Type at,
                                         NewtypeInners inners, Symbols symbols) {
            return of(operation, ObservationSource.asItStands(position), TakenArguments.NONE, at,
                    inners, symbols);
        }

        /** The same, for a taking the operation was given {@code arguments} beside the value at
         *  {@code position}. */
        public static TakenOf asItStands(ValueName.Stdlib operation, TermPath position,
                                         TakenArguments arguments, Type at, NewtypeInners inners,
                                         Symbols symbols) {
            return of(operation, ObservationSource.asItStands(position), arguments, at, inners,
                    symbols);
        }

        /**
         * The term for what {@code operation} answers of the value {@code source} says — the one
         * at its position, or what it was made into — or null where the two do not go together.
         *
         * <p><b>The one way one of these is made.</b> Four things have to hold and each of them is
         * a proposition somebody already owns: there is an account of what such a call takes, from
         * the declarations or from what they already say of the operation
         * ({@code check.BoundOperationFacts}), it answers a number ({@link NumericAnswers}), what
         * stands at the location is what that account is taken of ({@link TakenAs#takenOf}), and
         * what it was given beside that value settles which number is taken
         * ({@link TakenAs#settledBy}). The third was a premise the call sites carried — "the
         * operation and the location agree, by construction" — which is a claim about who happens
         * to build one today and not an invariant (#1027).
         *
         * <p>And a value made into something is one the account reads
         * ({@link TakenAs#readsWhatItWasMadeFrom}): every part of a moved date is a number a row is
         * written for.
         *
         * <p>Null and not a refusal. Whether a call names a number the model has a term for is a
         * question every reader of an expression asks, and the answer "it does not" is one they all
         * have somewhere to put: no line is drawn and the rule is reported as one nothing read.
         *
         * <p>Asked of what the names wrap, since a name around a list is still a list — the same
         * reach {@link Carrier#ofValue} takes, and taken here so that no caller takes it itself.
         */
        public static TakenOf of(ValueName.Stdlib operation, ObservationSource source,
                                 TakenArguments arguments, Type at, NewtypeInners inners,
                                 Symbols symbols) {
            TakenAs how = DefaultBoundOperationFacts.get().takenAs(operation, arguments);
            // Of what stands here, because for an operation that walks a container the answer is
            // what the container holds. Asked of the operation alone, a sum answered no number this
            // could name and no term was made for any rule written on one.
            Type answers = NumericAnswers.typeOf(operation, at, inners, symbols);
            if (how == null || answers == null || at == null || arguments == null
                    || source == null) {
                return null;
            }
            return how.takenOf(souther.compiler.check.TypeOps.base(at, inners), answers)
                    && how.settledBy(arguments)
                    && how.readsWhatItWasMadeFrom(source.transformation())
                    ? new TakenOf(operation, source, arguments) : null;
        }

        /** The operation whose answer this term is. */
        public ValueName.Stdlib operation() {
            return operation;
        }

        /** The same taking, of the value at the place {@code moved} puts this one's. What stands
         *  there is a value of the same type, so the account the operation is taken by holds of it
         *  as it did here. */
        @Override
        public TakenOf movedTo(PlacesMoved moved) {
            return new TakenOf(operation, source.movedTo(moved), arguments);
        }

        /** What it was given beside the value it takes its number of, read as constants — and
         *  nothing where it was given nothing. */
        public TakenArguments arguments() {
            return arguments;
        }

        @Override
        public TermPath position() {
            return source.position();
        }

        /** What the value the operation took its number of was made from the one at
         *  {@link #position()}, which is nothing where it is that one. */
        public ValueTransformation transformation() {
            return source.transformation();
        }

        /** The value the operation takes its number of: where it stands and what it was made
         *  into. */
        public ObservationSource source() {
            return source;
        }

        /**
         * Where the operation states its answers lie, of any value it could be given, with what it
         * was handed beside the value: a size at or above nought, an hour from nought to
         * twenty-three.
         *
         * <p>Without where the value it is taken of can stand, which {@link #intrinsicBounds} meets
         * this with: a date moved a year's days back is never the last date, and the year that keeps
         * it from is where dates stop being written rather than anything the operation answers.
         */
        public NumericDomain.Bounds whatTheOperationStates() {
            return ResultRange.of(DefaultBoundOperationFacts.get().boundsOnTheResult(operation),
                    argument -> Optional.ofNullable(arguments.at(argument.position())));
        }

        /** What this operation takes of the value at {@link #position()}, given what it was handed
         *  beside it. Never null: one of these cannot be built where there is no such account. */
        public TakenAs takenAs() {
            return DefaultBoundOperationFacts.get().takenAs(operation, arguments);
        }

        /** By the operation, the value it takes its number of and what it was given beside it,
         *  which is what makes two of these one term. */
        @Override
        public boolean equals(Object other) {
            return other instanceof TakenOf taken
                    && operation.equals(taken.operation) && source.equals(taken.source)
                    && arguments.equals(taken.arguments);
        }

        @Override
        public int hashCode() {
            return java.util.Objects.hash(operation, source, arguments);
        }

        @Override
        public String toString() {
            return operation.qualified() + arguments.writtenWith(
                    source.transformation().writtenAround(source.position().toString()));
        }
    }

    /**
     * How many of the code points of the string a location holds are in a class: the ones that are
     * not whitespace, that are neither whitespace nor one separator, or that are one of a set.
     *
     * <p>A number a rule can be about without any operation of the language answering it. What
     * {@code String.trim} leaves of a string holds something exactly where this is above nought,
     * the pieces a split by one code point leaves hold something between them under the same
     * condition, and some character of the string meets what is asked of it exactly where the
     * string holds a code point of the set a character meeting it is one of — so a rule about
     * any of them is a rule about this count of the string it was made from.
     * Nothing the language declares is a taking of it: a term {@link TakenOf} stands for is an
     * operation's answer, this is a quantity the reading works out, and the two are kept apart so
     * that a taking is still only of an operation that declares one.
     *
     * <p>Counted by what the run time counts by: in scalar values, against the one whitespace
     * alphabet the library's own operations scan with ({@link CodePointClass}).
     *
     * <p>Of the string as it stands or of what a case conversion answers of it ({@link
     * CaseMapping}). The second is a number of the string all the same: the conversion is the run
     * time's, so the count is whatever the run time's answer holds, and it is worked out of that
     * answer and never from the classes the code points of the string are in.
     *
     * <p>Only of a string. The number a count of one string's code points comes to is bounded by
     * the string's own length, and where a rule is also drawn on that length the two are one
     * string's numbers and are realized together. A conversion can write more code points than it
     * was given, so a count of what it answers has no such bound, and the numbers of one string
     * are not added up code point by code point.
     */
    final class CodePointClassCount implements FromOnePosition {

        private final TermPath position;
        private final CodePointClass counted;
        private final CaseMapping through;

        private CodePointClassCount(TermPath position, CodePointClass counted,
                                    CaseMapping through) {
            this.position = Objects.requireNonNull(position, "counted of somewhere");
            this.counted = Objects.requireNonNull(counted, "and of some code points");
            this.through = Objects.requireNonNull(through, "of the string or of what it maps to");
        }

        /**
         * The count of the code points, in {@code counted}, of what {@code through} makes of the
         * string at {@code position}, or null where what stands there is no string.
         *
         * <p>Asked of what the names wrap, as a taking is: a name around a string is still one.
         */
        public static CodePointClassCount of(TermPath position, CodePointClass counted,
                                             CaseMapping through, Type at, NewtypeInners inners) {
            return at != null && TypeOps.base(at, inners) == Type.STRING
                    ? new CodePointClassCount(position, counted, through) : null;
        }

        /** The code points this counts. */
        public CodePointClass counted() {
            return counted;
        }

        /** What the string is made into before its code points are counted. */
        public CaseMapping through() {
            return through;
        }

        @Override
        public TermPath position() {
            return position;
        }

        @Override
        public CodePointClassCount movedTo(PlacesMoved moved) {
            return new CodePointClassCount(moved.put(position), counted, through);
        }

        @Override
        public boolean equals(Object other) {
            return other instanceof CodePointClassCount count
                    && position.equals(count.position) && counted.equals(count.counted)
                    && through.equals(count.through);
        }

        @Override
        public int hashCode() {
            return Objects.hash(position, counted, through);
        }

        @Override
        public String toString() {
            return "#(" + counted + ")(" + through.writtenAround(position.toString()) + ")";
        }
    }

    /**
     * What the code points of the string a location holds come to, each added as the number it is.
     *
     * <p>A number of one string, as how long it is and how many of its code points are in a class
     * are: what a total of the list of its code points answers ({@code ListsTheCodePointsOf}) is
     * read off the string a row holds and written by writing a string. Not a taking: the operation
     * that answers it adds up a container, and what would be composed for a container is elements,
     * which a string is not written out of. Kept apart so that a total stays something a container
     * is built to have, and this something a string is chosen for.
     *
     * <p>Counted by what the run time counts by: scalar values, of the string as it is held.
     */
    final class CodePointValueSum implements FromOnePosition {

        private final TermPath position;

        private CodePointValueSum(TermPath position) {
            this.position = Objects.requireNonNull(position, "added up of somewhere");
        }

        /**
         * What the code points of the string at {@code position} come to, or null where what
         * stands there is no string.
         *
         * <p>Asked of what the names wrap, as a taking is: a name around a string is still one.
         */
        public static CodePointValueSum of(TermPath position, Type at, NewtypeInners inners) {
            return at != null && TypeOps.base(at, inners) == Type.STRING
                    ? new CodePointValueSum(position) : null;
        }

        @Override
        public TermPath position() {
            return position;
        }

        @Override
        public CodePointValueSum movedTo(PlacesMoved moved) {
            return new CodePointValueSum(moved.put(position));
        }

        @Override
        public boolean equals(Object other) {
            return other instanceof CodePointValueSum sum && position.equals(sum.position);
        }

        @Override
        public int hashCode() {
            return Objects.hash(CodePointValueSum.class, position);
        }

        @Override
        public String toString() {
            return "List.sum(String.codePoints(" + position + "))";
        }
    }

    /**
     * The code point of the string at {@code position} standing at {@code index} of the list
     * {@code String.codePoints} answers of it, counted from nought.
     *
     * <p>A number of one string, as what its code points come to is, and never a number of its own:
     * two of these at one string are two places of one value, so a row holding both writes one
     * string with each of them where it stands, and not a string for each. Read only where the
     * string is proved to hold the index — how long it is is settled by its rules — so a string
     * too short to hold it is one no row of the reading that made this has.
     *
     * <p>Counted by what the run time counts by: scalar values, of the string as it is held.
     */
    final class CodePointAt implements FromOnePosition {

        private final TermPath position;
        private final int index;

        private CodePointAt(TermPath position, int index) {
            this.position = Objects.requireNonNull(position, "a code point of somewhere");
            if (index < 0) {
                throw new IllegalArgumentException("a code point stands at an index from nought on: "
                        + index);
            }
            this.index = index;
        }

        /**
         * The code point at {@code index} of the string at {@code position}, or null where what
         * stands there is no string.
         */
        public static CodePointAt of(TermPath position, int index, Type at, NewtypeInners inners) {
            return at != null && TypeOps.base(at, inners) == Type.STRING
                    ? new CodePointAt(position, index) : null;
        }

        @Override
        public TermPath position() {
            return position;
        }

        /** Where in the string's code points this stands, counted from nought. */
        public int index() {
            return index;
        }

        @Override
        public CodePointAt movedTo(PlacesMoved moved) {
            return new CodePointAt(moved.put(position), index);
        }

        /**
         * Read off the string and, of it, the one index: a code point at another index of the
         * string is read off another place of it, and one read off the whole string — its length,
         * what its code points come to — is read off this one too. Which values the two places
         * take together is still the string's format's to say, and a row holding both is the one
         * string written with each where it stands.
         */
        @Override
        public boolean sharesAPlaceWith(NumericTerm other) {
            return (other instanceof CodePointAt at && position.equals(at.position))
                    ? index == at.index : FromOnePosition.super.sharesAPlaceWith(other);
        }

        @Override
        public boolean equals(Object other) {
            return other instanceof CodePointAt at && position.equals(at.position)
                    && index == at.index;
        }

        @Override
        public int hashCode() {
            return Objects.hash(CodePointAt.class, position, index);
        }

        @Override
        public String toString() {
            return "List.get(" + index + ", String.codePoints(" + position + "))";
        }
    }

    /**
     * How the steps an operation counts of the value at a position are made: against the type of
     * what stands there, which only the reading of the input knows — or null where they are not of
     * it.
     */
    @FunctionalInterface
    interface StepsAt {

        WholeUnitsOf of(ValueName.Stdlib operation, TermPath position);
    }

    /**
     * The step of a coarser order that the value at {@code position} falls in, as the operation
     * says: {@code DateTime.toDate} of a date-time is the day its second falls in.
     *
     * <p>A number of one value, counted on the order the operation answers: the step is
     * {@code floor(count / perUnit)} of the count the value stands at, with {@code perUnit} the
     * operation's own declaration ({@code CountsTheWholeUnitsOf}) and not a number kept here. What a
     * comparison of it states of the value is stated through the steps the value falls in, which is
     * the pullback the readers of a comparison take, and the term is no form of the value.
     *
     * <p>Keyed by the operation the call resolved to, so two operations declaring the same unit are
     * two terms.
     */
    final class WholeUnitsOf implements FromOnePosition {

        private final ValueName.Stdlib operation;
        private final TermPath position;
        /** The steps some value of the position's type falls in, or null where that is not worked
         *  out. Not part of which number this is: it follows from the operation and the type of
         *  what stands at the position, which a position has one of. */
        private final NumericDomain.Bounds image;
        /** Whether every step of the answer's order is one of them. */
        private final boolean fills;

        private WholeUnitsOf(ValueName.Stdlib operation, TermPath position,
                             NumericDomain.Bounds image, boolean fills) {
            this.operation = Objects.requireNonNull(operation, "taken by an operation");
            this.position = Objects.requireNonNull(position, "of somewhere");
            this.image = image;
            this.fills = fills;
        }

        /**
         * The steps of the order {@code operation} answers that the value at {@code position}
         * falls in, or null where the operation declares no such count or what stands there is not
         * what it counts.
         *
         * <p>The one way one is made: the operation and the type of the value go together here and
         * nowhere else, and what the steps reach is worked out from the two orders at the same
         * time ({@link #stepsFallenInto}), so a term that exists has an answer to whether its
         * steps are all there are.
         */
        public static WholeUnitsOf of(ValueName.Stdlib operation, TermPath position, Type at,
                                      NewtypeInners inners, DeclarationAccess declarations) {
            BoundOperationFacts facts = DefaultBoundOperationFacts.get();
            Type counted = facts.wholeUnitsCountedOn(operation);
            Type answers = facts.wholeUnitsAnswered(operation);
            Type base = at == null ? null : TypeOps.base(at, inners);
            Carrier observed = base == null || counted == null ? null
                    : Carrier.ofValue(base, declarations);
            Carrier answered = answers == null ? null : Carrier.ofValue(answers, declarations);
            if (observed == null || answered == null || !observed.counts()
                    || !counted.equals(base)) {
                return null;
            }
            long perUnit = facts.wholeUnitsPerStep(operation).orElseThrow();
            return new WholeUnitsOf(operation, position,
                    stepsFallenInto(observed, answered, perUnit),
                    stepsFill(observed, answered, perUnit));
        }

        /** The steps some value of the position's type falls in, or null where that is not worked
         *  out. */
        public NumericDomain.Bounds image() {
            return image;
        }

        /** Whether every step of the answer's order is one some value of the position's type falls
         *  in: whether a reader may take a row to stand at any of them. */
        public boolean stepsFillTheAnswersOrder() {
            return fills;
        }

        /**
         * The steps of the order {@code answered} that some value of the order {@code observed}
         * falls in, when {@code perUnit} steps of the second make one of the first — or null where
         * an end of {@code observed} is not a value it holds, so that what it reaches is not
         * worked out.
         *
         * <p>The one place that says which steps a value falls in, and so the one place a reader
         * learns whether they are all of the steps there are. A declaration of the unit says what a
         * step is and nothing of what the values reach: the seconds of a day fall in one step, and
         * counted in hours they fill twenty-four of the integers and not the integers.
         *
         * <p>Worked out of the ends of the two orders. A step keeps the order of the count it is
         * the step of, and consecutive counts fall in consecutive steps or the same one, so the
         * steps are every whole number from the step of the first count to the step of the last.
         */
        public static NumericDomain.Bounds stepsFallenInto(Carrier observed, Carrier answered,
                                                           long perUnit) {
            Endpoint low = stepOfTheEnd(observed.extent().low(), perUnit);
            Endpoint high = stepOfTheEnd(observed.extent().high(), perUnit);
            boolean unknown = (observed.extent().low() != null && low == null)
                    || (observed.extent().high() != null && high == null);
            return unknown ? null : new NumericDomain.Bounds(low, high).meet(
                    new NumericDomain.Bounds(answered.extent().low(), answered.extent().high()));
        }

        /**
         * Whether every step of the order {@code answered} is one some value of {@code observed}
         * falls in: what a reader may take for a run every value of which some row stands at.
         */
        public static boolean stepsFill(Carrier observed, Carrier answered, long perUnit) {
            NumericDomain.Bounds fallenInto = stepsFallenInto(observed, answered, perUnit);
            return fallenInto != null && new NumericDomain.Bounds(answered.extent().low(),
                    answered.extent().high()).liesWithin(fallenInto);
        }

        /**
         * The steps the values fall in where the rules hold them to {@code values}: each end taken
         * to the step it falls in, which keeps the order, so every value of the run falls in a step
         * of the one it is taken to. An end a run leaves out is taken as one it holds, so the steps
         * are the ones the run could fall in and never fewer — or null where an end is not a count.
         *
         * <p>What the rules hold the end of some steps to is this and the steps' own image
         * ({@link #image}) together: a lower bound on the seconds is a lower bound on the days.
         */
        public NumericDomain.Bounds stepsFallenIntoBy(NumericDomain.Bounds values) {
            if (values == null) {
                return null;
            }
            Endpoint low = stepOfAnEnd(values.min(), perUnit(), true);
            Endpoint high = stepOfAnEnd(values.max(), perUnit(), true);
            boolean unknown = (values.min() != null && low == null)
                    || (values.max() != null && high == null);
            return unknown ? null : new NumericDomain.Bounds(low, high);
        }

        private static Endpoint stepOfTheEnd(Endpoint end, long perUnit) {
            return stepOfAnEnd(end, perUnit, false);
        }

        /** The step the count at {@code end} falls in, as an end; null where there is no end or it
         *  is not a count the value holds, or — unless {@code widening} — it is left out. */
        private static Endpoint stepOfAnEnd(Endpoint end, long perUnit, boolean widening) {
            if (end == null || (!widening && !end.inclusive())
                    || !(end.at() instanceof Count count)) {
                return null;
            }
            return ExactRatio.of(count.at()).dividedBy(ExactRatio.of(perUnit))
                    .flatMap(ExactRatio::floor) instanceof ExactAnswer.Held<BigInteger>(var step)
                    ? Endpoint.inclusive(new Count(new BigDecimal(step))) : null;
        }

        /** The operation whose answer this term is. */
        public ValueName.Stdlib operation() {
            return operation;
        }

        /** How many steps of the value's order make one step of the answer's. */
        public long perUnit() {
            return DefaultBoundOperationFacts.get().wholeUnitsPerStep(operation).orElseThrow();
        }

        @Override
        public TermPath position() {
            return position;
        }

        @Override
        public WholeUnitsOf movedTo(PlacesMoved moved) {
            return new WholeUnitsOf(operation, moved.put(position), image, fills);
        }

        @Override
        public boolean equals(Object other) {
            return other instanceof WholeUnitsOf units && operation.equals(units.operation)
                    && position.equals(units.position);
        }

        @Override
        public int hashCode() {
            return Objects.hash(WholeUnitsOf.class, operation, position);
        }

        @Override
        public String toString() {
            return operation + "(" + position + ")";
        }
    }

    /**
     * How many elements of a container hold, at one place inside the element, the value the
     * element under consideration holds there.
     *
     * <p>A number of an element, read off the container it stands in: every element of a list of
     * keys is a key, and it occurs as many times as the list holds that key. What a fold that files
     * a counter under each key answers for the key of an element is this number, shifted and scaled
     * by what the fold starts the counter at and adds to it. Nothing the language declares takes
     * it of a value — it is a quantity the reading works out — so it is kept apart from
     * {@link TakenOf}, which is only ever an operation's answer.
     *
     * <p>The element is whichever one a statement about some element of the container is about, so
     * this is one number for each element and no number of the container. Two elements holding the
     * same value at {@code place} read the same number, and every element reads at least one, since
     * it is one of those it counts.
     */
    final class Multiplicity implements OfAnElementsNeighbours {

        private final TermPath container;
        private final TermPath place;

        private Multiplicity(TermPath container, TermPath place) {
            this.container = Objects.requireNonNull(container, "counted among a container's elements");
            this.place = Objects.requireNonNull(place, "by the value standing at a place");
        }

        /**
         * The number of times the value at {@code place} occurs among the elements of
         * {@code container}, or null where {@code place} is not reached from an element of it by
         * fields alone, where an element may hold many values there or none.
         *
         * @param container the container whose elements are counted
         * @param place     where, inside an element of {@code container}, the value compared stands
         */
        public static Multiplicity of(TermPath container, TermPath place) {
            return container != null && place != null && fieldsBelowAnElement(container, place)
                    ? new Multiplicity(container, place) : null;
        }

        /** The container whose elements are counted. */
        @Override
        public TermPath container() {
            return container;
        }

        /** Where the value compared stands, inside an element of {@link #container()}. */
        public TermPath place() {
            return place;
        }

        /** The way from an element of the container to {@link #place()}. */
        public ElementProjection placeField() {
            return fieldsTo(container, place);
        }

        @Override
        public List<ElementProjection> fieldsRead() {
            return List.of(placeField());
        }

        /** Where the value compared stands, which is where a reader is sent and no place the
         *  number stands at. */
        @Override
        public TermPath subjectPath() {
            return place;
        }

        /** The same number of where {@code moved} puts its places, or null where the place moved is
         *  no longer one value of each element of the container moved. */
        @Override
        public Multiplicity movedTo(PlacesMoved moved) {
            return of(moved.put(container), moved.put(place));
        }

        @Override
        public boolean equals(Object other) {
            return other instanceof Multiplicity that
                    && container.equals(that.container) && place.equals(that.place);
        }

        @Override
        public int hashCode() {
            return Objects.hash(container, place);
        }

        @Override
        public String toString() {
            return "multiplicity(" + place + ")";
        }
    }

    /**
     * The least or the greatest of the values the elements of a container hold at one place, among
     * the elements holding at another place what the element under consideration holds there.
     *
     * <p>A number of an element read off the elements beside it, as {@link Multiplicity} is: what a
     * fold that keeps one end of what it files under each key answers for the key of an element is
     * this number, and the elements of one key all read the same one. It is not the value the
     * element holds. Of two elements of one key holding four and ten, the least is four for both,
     * so a statement that some element's least is at least seven is false where one that some
     * element holds at least seven is true — which is why this is a term of its own and not the
     * value at {@link #value()}.
     *
     * <p>Every element reads one of the values of its key, so the number is among the values the
     * place holds; an element alone under its key reads its own.
     */
    final class ExtremeOfItsKey implements OfAnElementsNeighbours {

        private final TermPath container;
        private final TermPath key;
        private final TermPath value;
        private final Extreme extreme;
        private final WholeUnitsOf steps;

        private ExtremeOfItsKey(TermPath container, TermPath key, TermPath value,
                                Extreme extreme, WholeUnitsOf steps) {
            this.container = Objects.requireNonNull(container, "taken among a container's elements");
            this.key = Objects.requireNonNull(key, "of the elements alike at one place");
            this.value = Objects.requireNonNull(value, "of what they hold at another");
            this.extreme = Objects.requireNonNull(extreme, "and one end of it");
            this.steps = steps;
        }

        /**
         * The same, of the steps {@code steps} counts of the values — the day the latest second
         * falls on — or null where {@code steps} is not of the value at {@code value}.
         *
         * <p>A step keeps the order of what it is the step of, so the end of the steps is the step
         * of the end, and this is one number however many elements an end is taken among. The
         * steps are a term that was made against the type of the value, so an operation and a value
         * of another type are never met here.
         */
        public static ExtremeOfItsKey of(TermPath container, TermPath key, TermPath value,
                                         Extreme extreme, WholeUnitsOf steps) {
            if (steps != null && !steps.position().equals(value)) {
                return null;
            }
            return container != null && key != null && value != null && extreme != null
                    && fieldsBelowAnElement(container, key)
                    && fieldsBelowAnElement(container, value)
                    ? new ExtremeOfItsKey(container, key, value, extreme, steps) : null;
        }

        /**
         * The {@code extreme} of what the elements of {@code container} hold at {@code value},
         * among those holding at {@code key} what the element under consideration holds there — or
         * null where either place is not reached from an element of it by fields alone, where an
         * element may hold many values there or none.
         */
        public static ExtremeOfItsKey of(TermPath container, TermPath key, TermPath value,
                                         Extreme extreme) {
            return of(container, key, value, extreme, null);
        }

        /**
         * The same, with the key named by the fields read from the element the value at
         * {@code value} stands in — or null where the value stands in no container.
         */
        public static ExtremeOfItsKey ofTheValueAt(TermPath value, List<String> key,
                                                   Extreme extreme) {
            return ofTheValueAt(value, key, extreme, null);
        }

        /** The same, of the steps {@code steps} counts of the values. */
        public static ExtremeOfItsKey ofTheValueAt(TermPath value, List<String> key,
                                                   Extreme extreme, WholeUnitsOf steps) {
            List<TermPath> holding = value.containersHoldingIt();
            if (holding.isEmpty()) {
                return null;
            }
            TermPath container = holding.getLast();
            return of(container, ElementProjection.ofFields(key).from(container.element()), value,
                    extreme, steps);
        }

        /** The steps of the values this is the end of, or null where it is the end of the values
         *  themselves. */
        public WholeUnitsOf steps() {
            return steps;
        }

        /** The operation whose steps of the values this is the end of, or null where it is the end
         *  of the values themselves. */
        public ValueName.Stdlib through() {
            return steps == null ? null : steps.operation();
        }

        /** How many steps of the values' order make one of the steps this is the end of. */
        public long perUnit() {
            return steps.perUnit();
        }

        /** The way from an element of the container to {@link #key()}. */
        public ElementProjection keyField() {
            return fieldsTo(container, key);
        }

        /** The way from an element of the container to {@link #value()}. */
        public ElementProjection valueField() {
            return fieldsTo(container, value);
        }

        @Override
        public List<ElementProjection> fieldsRead() {
            return List.of(keyField(), valueField());
        }

        /** The container whose elements are looked at. */
        @Override
        public TermPath container() {
            return container;
        }

        /** Where, inside an element, what makes two elements of one key stands. */
        public TermPath key() {
            return key;
        }

        /** Where, inside an element, the values one end of which is taken stand. */
        public TermPath value() {
            return value;
        }

        /** Which end of them is taken. */
        public Extreme extreme() {
            return extreme;
        }

        /**
         * The number this one is always one of the values of: what stands at {@link #value()}, or
         * the steps those values fall in where this is the end of the steps.
         *
         * <p>Which values this number can take — the run the rules leave it, the set a place
         * admits — is that number's question, since an end of some of the values is one of them.
         * Whether a row exists holding one at it is not: that takes a container holding the
         * elements, which no answer about the values says exists.
         *
         * <p>In the order this number is counted on, which is the answer's for the steps. Handed
         * the value itself, a reader asking what the end can be would be answered in the units of
         * the seconds for a number of days.
         */
        public FromOnePosition valuesTakenFrom() {
            return steps != null ? steps : new ValueOf(value);
        }

        /** Where the values one end of which is taken stand, which is where a reader is sent and no
         *  place the number stands at. */
        @Override
        public TermPath subjectPath() {
            return value;
        }

        /** The same number of where {@code moved} puts its places, or null where the places moved
         *  are no longer one value of each element of the container moved. */
        @Override
        public ExtremeOfItsKey movedTo(PlacesMoved moved) {
            return of(moved.put(container), moved.put(key), moved.put(value), extreme,
                    steps == null ? null : steps.movedTo(moved));
        }

        @Override
        public boolean equals(Object other) {
            return other instanceof ExtremeOfItsKey that && container.equals(that.container)
                    && key.equals(that.key) && value.equals(that.value)
                    && extreme.equals(that.extreme) && Objects.equals(steps, that.steps);
        }

        @Override
        public int hashCode() {
            return Objects.hash(container, key, value, extreme, steps);
        }

        @Override
        public String toString() {
            return new NumberAt.OfWhatNumber.OfTheExtremeOfItsKey(extreme, keyField().fields(),
                    through()).spelledAt(value.toString());
        }
    }

    /**
     * How many of the values in every occurrence of a place inside more than one container equal
     * the one an element stands at: how often a key occurs among the lists of an outer list put
     * end to end.
     *
     * <p>A number of one value, as {@link Multiplicity} is, but counted among a run and not among
     * the elements of one occurrence of a container. The lists of two orders are two sets of
     * lines, and a line of one is no neighbour of a line of the other; a list made of the lines of
     * every order holds them all, so the same value in two orders is two of its occurrences. The
     * run is {@link RunSource.FlattenedOccurrences}, which is made only where a walk was shown to
     * be over every occurrence of the place, so a count of it is a count of everything standing
     * there and of nothing twice.
     *
     * <p>Equal as the place's order has them, and one for each value standing at the place: the
     * value under consideration is whichever one a reading chose, and it is one of the values it
     * counts.
     */
    final class OccurrencesOfItsValue implements NumericTerm {

        private final RunSource run;
        private final KeptOccurrences selection;

        private OccurrencesOfItsValue(RunSource run, KeptOccurrences selection) {
            this.run = Objects.requireNonNull(run, "counted among the values of a run");
            this.selection = selection;
        }

        /** The number of times the value standing at a place of {@code run} occurs among all of
         *  them. */
        public static OccurrencesOfItsValue of(RunSource.FlattenedOccurrences run) {
            return run == null ? null : new OccurrencesOfItsValue(run, null);
        }

        /**
         * The number of times the value standing at a place of {@code run} occurs among those of
         * its occurrences {@code selection} keeps — or null where the run is neither the values
         * of one container's elements nor of many containers'.
         *
         * <p>Only a value that is kept has a number: an occurrence the selection drops is no
         * entry of the map a fold files, so it has no count to be compared with. Every kept
         * occurrence counts at least itself.
         */
        public static OccurrencesOfItsValue of(RunSource run, KeptOccurrences selection) {
            return run instanceof RunSource.ProjectedOccurrences
                    || run instanceof RunSource.FlattenedOccurrences
                    ? new OccurrencesOfItsValue(run, selection) : null;
        }

        /** The run whose values are counted. */
        public RunSource run() {
            return run;
        }

        /**
         * Which of the occurrences are counted, or null where every one is.
         *
         * <p>Held with the statement put to rows because the readers of a term — a read back
         * value, a row's reading, a composed container — are given the term and a row and no
         * reading of the input to build that statement from. What names the quantity is the
         * container and the statement the selection keeps by, which is all its equality and its
         * report coordinate use; the statement put to rows is derived from them and is no part of
         * which quantity this is.
         */
        public KeptOccurrences selection() {
            return selection;
        }

        /** Where the values counted stand, which is where a reader is sent and no place the number
         *  stands at. */
        @Override
        public TermPath subjectPath() {
            return run.subjectPath();
        }

        /** The same number of the run read from where {@code moved} puts this one's — or null
         *  where that is no run this counts among ({@link #of(RunSource, KeptOccurrences)}), or
         *  the move takes a place the selection reads elsewhere
         *  ({@link NumericTerm#selectionStays}). */
        @Override
        public OccurrencesOfItsValue movedTo(PlacesMoved moved) {
            RunSource at = run.movedTo(moved);
            return NumericTerm.selectionStays(selection, moved) ? of(at, selection) : null;
        }

        @Override
        public boolean equals(Object other) {
            return other instanceof OccurrencesOfItsValue that && run.equals(that.run)
                    && Objects.equals(selection, that.selection);
        }

        @Override
        public int hashCode() {
            return Objects.hash(OccurrencesOfItsValue.class, run, selection);
        }

        @Override
        public String toString() {
            return selection == null ? "occurrences(" + run + ")"
                    : "occurrences(" + run + " kept by " + selection.key() + ")";
        }
    }

    /**
     * How many of the values of a run are equal to the value an input holds at {@code key}: the
     * occurrences of a key asked for among the lists of an outer list put end to end.
     *
     * <p>Where {@link OccurrencesOfItsValue} counts the occurrences of a value that is one of the
     * run's, and so counts at least that one, this counts the occurrences of a value that is
     * outside it, and is nought where the key is among none. The two are one count only where the
     * key is one of the values of the run.
     *
     * <p>The value of {@code key} is chosen with the rest of the row, and the run is the occurrences
     * of a place no row holds as one position, so the number stands at neither: {@link
     * #subjectPath} is where a reader is sent.
     */
    final class OccurrencesOfAKey implements NumericTerm {

        private final RunSource.FlattenedOccurrences run;
        private final TermPath key;

        private OccurrencesOfAKey(RunSource.FlattenedOccurrences run, TermPath key) {
            this.run = Objects.requireNonNull(run, "counted among the values of a run");
            this.key = Objects.requireNonNull(key, "counted as often as a key occurs");
        }

        /** The number of values of {@code run} equal to the one at {@code key}, which stands
         *  outside every container. */
        public static OccurrencesOfAKey of(RunSource.FlattenedOccurrences run, TermPath key) {
            return run == null || key == null || key.insideAContainer() ? null
                    : new OccurrencesOfAKey(run, key);
        }

        /** The run whose values are counted. */
        public RunSource.FlattenedOccurrences run() {
            return run;
        }

        /** Where the value counted for stands. */
        public TermPath key() {
            return key;
        }

        /** Where the values counted stand, which is where a reader is sent and no place the number
         *  stands at. */
        @Override
        public TermPath subjectPath() {
            return run.subjectPath();
        }

        /** The same number read from where {@code moved} puts the run and the key — or null where
         *  that is no run of every occurrence, or the key stands inside a container. */
        @Override
        public OccurrencesOfAKey movedTo(PlacesMoved moved) {
            return run.movedTo(moved) instanceof RunSource.FlattenedOccurrences flat
                    ? of(flat, moved.put(key)) : null;
        }

        @Override
        public List<TermPath> placesReadOff() {
            return List.of(run.subjectPath(), key);
        }

        @Override
        public boolean equals(Object other) {
            return other instanceof OccurrencesOfAKey that && run.equals(that.run)
                    && key.equals(that.key);
        }

        @Override
        public int hashCode() {
            return Objects.hash(OccurrencesOfAKey.class, run, key);
        }

        @Override
        public String toString() {
            return "occurrences(" + run + " equal to " + key + ")";
        }
    }

    /**
     * What the elements of a run come to together, among those holding at {@link #key()} what the
     * element under consideration holds there: the total of the number each of them is, or one end
     * of those numbers. What a fold that files under each key what that key's elements come to
     * answers for the key of an element.
     *
     * <p>A number of the run and not of one container's elements, which is why it is not one of
     * {@link OfAnElementsNeighbours}: the elements may stand in every occurrence of a container
     * inside another, the lists of an outer list put end to end, and an element of one is then
     * gathered with an element of another under one key. Made only where a walk was shown to be
     * over every occurrence of the place the elements stand at, as {@link
     * RunSource.FlattenedOccurrences} is.
     *
     * <p>What each element contributes is {@link #value()}, a number made of the element, and not a
     * place: a field of the element is the one such number that is a place ({@link
     * ElementValue#asAPlace}), and a number a closure computed of the element stands nowhere in it.
     * So the totals of {@code p.amount} and of {@code signed(p)} are two numbers of one run, and
     * neither is a value standing at a position.
     *
     * <p>The end of the values of a place inside one container is {@link ExtremeOfItsKey}, which
     * reads it among the elements of that container's one occurrence; this does not take that
     * number, so it is spelled one way.
     */
    final class GatheredUnderItsKey implements NumericTerm {

        /**
         * How the numbers of the elements of one key are put together.
         *
         * <p>Sealed, and one arm per law, as {@code KeyedAccumulation.Filed} is: a reader of what
         * a key comes to says what it is under each.
         */
        public sealed interface Gathering {

            /** Every number of the key added up. */
            record Total() implements Gathering {}

            /** The least or the greatest of them. */
            record End(Extreme extreme) implements Gathering {

                public End {
                    Objects.requireNonNull(extreme, "an end is one end or the other");
                }
            }

            /**
             * The numbers of the key added up from the last element handed, in {@code order},
             * whose case at {@code subject} is one of {@code puts}, that element's number
             * included; every number of the key where none of them is.
             *
             * <p>Which element was handed last is the order and not the elements, so the order
             * is part of what this is: the same elements handed from the other end come to
             * another number. It holds what showed the order ({@link RunSource.TraversalOrder}),
             * and is made only where something did.
             *
             * @param subject where in the element the case that says whether it puts stands
             * @param puts    the cases of it whose elements put their number in place of the
             *                ones before
             * @param order   the direction the walk was handed the elements in
             */
            record SinceAPut(ElementProjection subject, List<CasesLeft> puts,
                             RunSource.TraversalOrder order) implements Gathering {

                public SinceAPut {
                    Objects.requireNonNull(subject, "a case is of some place of the element");
                    Objects.requireNonNull(order, "which element was handed last turns on the"
                            + " order they were handed in");
                    puts = List.copyOf(puts);
                    if (puts.isEmpty()) {
                        throw new IllegalArgumentException("some case puts, or it is a total");
                    }
                }
            }

            Gathering TOTAL = new Total();
        }

        private final TermPath elements;
        private final ElementKey key;
        private final ElementValue value;
        private final Type each;
        private final Gathering gathering;
        private final KeptOccurrences selection;
        /** The hash, worked out once: the computation is a tree, and a term is asked for its hash
         *  by every reading that files it. */
        private final int hash;

        private GatheredUnderItsKey(TermPath elements, ElementKey key, ElementValue value,
                                    Type each, Gathering gathering, KeptOccurrences selection) {
            this.elements = elements;
            this.key = key;
            this.value = value;
            this.each = each;
            this.gathering = gathering;
            this.selection = selection;
            this.hash = Objects.hash(GatheredUnderItsKey.class, elements, key, value, each,
                    gathering, selection);
        }

        /**
         * What the elements standing at {@code elements} that hold at {@code key} what the element
         * under consideration holds there come to, each as {@code value}, by {@code gathering} —
         * or null where some element the key reads a way for holds nothing along it ({@link
         * ElementKey#heldByEveryElementItTakes}), the value reads where each element stands, or
         * the number is {@link ExtremeOfItsKey}'s.
         *
         * <p>Asked of elements a walk was shown to be over every occurrence of, and of no others:
         * the path alone says no such thing of a place inside more than one container.
         *
         * @param elements where each element of the run stands, inside one container or several
         * @param key      what makes two elements one key
         * @param value    what each element contributes
         * @param each      what one element's number stands as, with the names it is written under
         *                  taken off: what the numbers of a key come to is on its order
         * @param selection the occurrences gathered where a statement keeps some of them, or null
         *                  where every one is
         */
        public static GatheredUnderItsKey of(TermPath elements, ElementKey key,
                                             ElementValue value, Type each, Gathering gathering,
                                             KeptOccurrences selection) {
            GatheredUnderItsKey made = underAnyKey(elements, key, value, each, gathering,
                    selection);
            boolean ownPlaceInOneContainer = made != null && value.asAPlace() != null
                    && elements.containersHoldingIt().size() == 1;
            return gathering instanceof Gathering.End && ownPlaceInOneContainer
                    && selection == null ? null : made;
        }

        /**
         * The number the elements of each key come to by {@code gathering}, spelled the one way
         * it is spelled: the end of the values of a place inside one container, of every element
         * of it, is an {@link ExtremeOfItsKey}, and every other is this — or null where it is
         * neither.
         */
        public static NumericTerm spelled(TermPath elements, ElementKey key,
                                          ElementValue value, Type each, Gathering gathering,
                                          KeptOccurrences selection, StepsAt stepsAt) {
            if (selection == null && gathering instanceof Gathering.End(Extreme extreme)
                    && value != null
                    && value.asAPlace() instanceof ElementProjection place && elements != null
                    && elements.containersHoldingIt().size() == 1
                    && key instanceof ElementKey.At(ElementProjection one)
                    && one.fields() != null) {
                TermPath at = place.from(elements);
                return at == null ? null : ExtremeOfItsKey.ofTheValueAt(at, one.fields(), extreme);
            }
            // The end of the steps one place falls in is the step of the end of the place, so it
            // is the end of the place through the operation that counts them.
            ElementValue.StepsOfAPlace steps = value == null ? null
                    : ElementValue.asTheStepsOfAPlace(value);
            if (selection == null && gathering instanceof Gathering.End(Extreme extreme)
                    && steps != null && steps.weight().equals(ExactRatio.ONE)
                    && steps.constant().isZero() && elements != null
                    && elements.containersHoldingIt().size() == 1
                    && key instanceof ElementKey.At(ElementProjection one)
                    && one.fields() != null) {
                TermPath at = steps.place().from(elements);
                WholeUnitsOf made = at == null ? null : stepsAt.of(steps.operation(), at);
                return made == null ? null
                        : ExtremeOfItsKey.ofTheValueAt(at, one.fields(), extreme, made);
            }
            return of(elements, key, value, each, gathering, selection);
        }

        /**
         * The same, including the end of the values of a place inside one container, which {@link
         * #of} leaves to {@link ExtremeOfItsKey}: for the key an input holds ({@link
         * GatheredUnderAKey}) there is no other spelling of it.
         */
        static GatheredUnderItsKey underAnyKey(TermPath elements, ElementKey key,
                                               ElementValue value, Type each,
                                               Gathering gathering, KeptOccurrences selection) {
            // One value of every element along the way it is read: none of them where the element
            // is its own key.
            if (elements == null || key == null || value == null || each == null
                    || gathering == null || !elements.insideAContainer()
                    || !key.heldByEveryElementItTakes() || value.readsThePosition()) {
                return null;
            }
            // An order is shown of the elements where they stood, and says nothing of elements
            // standing anywhere else.
            if (gathering instanceof Gathering.SinceAPut(var _, var _, var order)
                    && !order.elements().equals(elements)) {
                return null;
            }
            // What keeps some of them is a statement about these elements and no others: the
            // elements of the container it keeps some of, or those of them of the cases they are
            // narrowed to.
            ElementProjection narrowed = selection == null ? null : ElementProjection.below(
                    selection.container().inputPosition().element(), elements);
            if (selection != null && (narrowed == null || !narrowed.steps().stream()
                    .allMatch(TermPath.Step.Refine.class::isInstance))) {
                return null;
            }
            return new GatheredUnderItsKey(elements, key, value, each, gathering, selection);
        }

        /** Where each element of the run stands. */
        public TermPath elements() {
            return elements;
        }

        /** What makes two elements one key. */
        public ElementKey key() {
            return key;
        }

        /** What each element contributes. */
        public ElementValue value() {
            return value;
        }

        /** What one element's number stands as. */
        public Type each() {
            return each;
        }

        /** How the numbers of one key are put together. */
        public Gathering gathering() {
            return gathering;
        }

        /**
         * Which of the occurrences are gathered, or null where every one is: an occurrence the
         * selection drops is filed under no key, and has no number of its own.
         *
         * <p>Held with the statement put to rows, as {@link OccurrencesOfItsValue#selection} is.
         */
        public KeptOccurrences selection() {
            return selection;
        }

        /**
         * The number this one is always one of the values of, where there is one: what stands at
         * the place an end is taken of. Null for a total, which is none of its numbers, and for an
         * end of what each element computed, which stands at no place.
         */
        public ValueOf valuesTakenFrom() {
            ElementProjection place = value.asAPlace();
            return gathering instanceof Gathering.End && place != null
                    ? new ValueOf(place.from(elements)) : null;
        }

        /** Every way from an element to a value this number is read from: what the key reads, and
         *  what the value reads. */
        public List<ElementProjection> fieldsRead() {
            Set<ElementProjection> read = new LinkedHashSet<>(key.reads());
            read.addAll(value.reads());
            if (gathering instanceof Gathering.SinceAPut(ElementProjection subject, var _, var _)) {
                read.add(subject);
            }
            return List.copyOf(read);
        }

        /** Where the values gathered stand where they are a place of the element, and where the
         *  elements do otherwise: where a reader is sent, and no place the number stands at. */
        @Override
        public TermPath subjectPath() {
            ElementProjection place = value.asAPlace();
            return place == null ? elements : place.from(elements);
        }

        /** The same number of the elements standing where {@code moved} puts them, or null where
         *  they are not in as many containers there, or the move takes a place the selection
         *  reads elsewhere ({@link NumericTerm#selectionStays}). */
        @Override
        public GatheredUnderItsKey movedTo(PlacesMoved moved) {
            TermPath at = moved.put(elements);
            return NumericTerm.selectionStays(selection, moved)
                    && at.containersHoldingIt().size() == elements.containersHoldingIt().size()
                    ? underAnyKey(at, key, value, each, gathering, selection) : null;
        }

        @Override
        public boolean equals(Object other) {
            return other instanceof GatheredUnderItsKey that && hash == that.hash
                    && elements.equals(that.elements) && key.equals(that.key)
                    && value.equals(that.value) && each.equals(that.each)
                    && gathering.equals(that.gathering)
                    && Objects.equals(selection, that.selection);
        }

        @Override
        public int hashCode() {
            return hash;
        }

        @Override
        public String toString() {
            ElementProjection place = value.asAPlace();
            String of = (place == null ? "{" + value + " | " + elements + "}"
                    : place.from(elements).toString())
                    + (selection == null ? "" : " kept by " + selection.key());
            return switch (gathering) {
                case Gathering.Total _ -> "total(" + of + " by " + key.spelled() + ")";
                // Handed in the order written, as a run read by where its elements stand is
                // spelled; the other way round says so.
                case Gathering.SinceAPut(ElementProjection subject, List<CasesLeft> puts,
                                         RunSource.TraversalOrder order) ->
                        "total(" + of + " from the last " + String.join(" or ", puts.stream()
                                .map(cases -> subject.narrowedTo(cases).spelled()).toList())
                                + (order.direction() == TraversalDirection.REVERSE
                                        ? " handed from the far end" : "")
                                + " by " + key.spelled() + ")";
                case Gathering.End(Extreme extreme) -> switch (extreme) {
                    case Extreme.Least _ -> "least";
                    case Extreme.Greatest _ -> "greatest";
                } + "(" + of + " by " + key.spelled() + ")";
            };
        }
    }

    /**
     * What the elements of a run come to together among those whose key is the value an input
     * holds at {@link #asked()}: the number {@link GatheredUnderItsKey} is for the key of the
     * element under consideration, read for a key outside the run.
     *
     * <p>As {@link OccurrencesOfAKey} is beside {@link OccurrencesOfItsValue}: the key is chosen
     * with the rest of the row, so the number stands at neither it nor the elements, and it is
     * nothing where no element has the key. {@link #subjectPath} is where a reader is sent.
     */
    final class GatheredUnderAKey implements NumericTerm {

        private final GatheredUnderItsKey gathered;
        private final TermPath asked;
        /** The hash, worked out once: a term is asked for its hash by every reading that files
         *  it. */
        private final int hash;

        private GatheredUnderAKey(GatheredUnderItsKey gathered, TermPath asked) {
            this.gathered = Objects.requireNonNull(gathered, "gathered under a key");
            this.asked = Objects.requireNonNull(asked, "gathered under the key an input holds");
            this.hash = Objects.hash(GatheredUnderAKey.class, gathered, asked);
        }

        /**
         * What the elements standing at {@code elements} come to, each as {@code value}, by
         * {@code gathering}, among those holding at {@code key} what the input holds at
         * {@code asked}, which stands outside every container — or null where
         * {@link GatheredUnderItsKey} reads none of them. The end of the values of a place inside
         * one container is read: nothing else spells it for a key asked for.
         */
        public static GatheredUnderAKey of(TermPath elements, ElementKey key,
                                           ElementValue value, Type each,
                                           GatheredUnderItsKey.Gathering gathering,
                                           TermPath asked) {
            return over(GatheredUnderItsKey.underAnyKey(elements, key, value, each, gathering,
                    null), asked);
        }

        /** Read only of a key every element holds at one place: what an input holds is compared
         *  with that place. */
        private static GatheredUnderAKey over(GatheredUnderItsKey gathered, TermPath asked) {
            return gathered == null || !(gathered.key() instanceof ElementKey.At)
                    || asked == null || asked.insideAContainer() ? null
                    : new GatheredUnderAKey(gathered, asked);
        }

        /** Where every element holds the key. */
        public ElementProjection key() {
            return ((ElementKey.At) gathered.key()).path();
        }

        /** What is gathered, for the key of whichever element is under consideration. */
        public GatheredUnderItsKey gathered() {
            return gathered;
        }

        /** Where the key gathered for stands. */
        public TermPath asked() {
            return asked;
        }

        /**
         * Whether the key is a field the number is made of, or one around or inside it: every
         * element of the key holds the key there, so each contributes it and the number is the
         * elements' share of that one value.
         */
        public boolean keyIsWhatIsAdded() {
            TermPath keyAt = key().from(gathered.elements());
            for (ElementProjection read : gathered.value().reads()) {
                TermPath readAt = read.from(gathered.elements());
                if (readAt.isAtOrUnder(keyAt) || keyAt.isAtOrUnder(readAt)) {
                    return true;
                }
            }
            return false;
        }

        /**
         * Whether each element contributes its key and nothing else, so that the number is the
         * key itself where the elements of a key are one, and is the key as often as the key
         * occurs where they are several. The number a row is at then fixes the key: the key is
         * chosen with it and not before.
         */
        public boolean keyIsEachElementsNumber() {
            ElementProjection place = gathered.value().asAPlace();
            return place != null && place.from(gathered.elements())
                    .equals(key().from(gathered.elements()));
        }

        /** Where the elements stand, which is where a reader is sent and no place the number
         *  stands at. */
        @Override
        public TermPath subjectPath() {
            return gathered.elements();
        }

        /** The same number of the elements and the key standing where {@code moved} puts them —
         *  or null where the elements are not in as many containers there, or the key stands
         *  inside one. */
        @Override
        public GatheredUnderAKey movedTo(PlacesMoved moved) {
            GatheredUnderItsKey at = gathered.movedTo(moved);
            return at == null ? null : over(at, moved.put(asked));
        }

        @Override
        public boolean equals(Object other) {
            return other instanceof GatheredUnderAKey that && hash == that.hash
                    && gathered.equals(that.gathered) && asked.equals(that.asked);
        }

        @Override
        public int hashCode() {
            return hash;
        }

        @Override
        public String toString() {
            return gathered + " equal to " + asked;
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
        /**
         * The hash of the two, worked out once. A run computed of each element holds the whole
         * computation, which a term keyed into a set or a map would otherwise walk again each time
         * it is asked — and a term is asked many times over, by every reading that files it.
         */
        private final int hash;

        private TakenOver(ValueName.Stdlib operation, RunSource source) {
            this.operation = operation;
            this.source = source;
            this.hash = Objects.hash(operation, source);
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
                                   NewtypeInners inners, Symbols symbols) {
            TakenAs how = DefaultBoundOperationFacts.get().takenAs(operation);
            // A container of what the run holds, with the names its values are written under taken
            // off — the same reach {@link TakenOf#of} takes of the value at a place, and for the
            // same reason: a name wrapped round a whole number is what the account is taken of.
            Type over = each == null ? null
                    : new Type.ListOf(souther.compiler.check.TypeOps.base(each, inners));
            Type answers = over == null ? null
                    : NumericAnswers.typeOf(operation, over, inners, symbols);
            // How many values a run over one container holds is how many that container does, a
            // taking of the container's place and no number of its own. A run no one container
            // holds — every occurrence of a place inside several — has its count as a number of
            // the run.
            if (how == null || answers == null || source == null
                    || (how instanceof TakenAs.HowManyItHolds && source.isInOneContainer())) {
                return null;
            }
            return how.takenOf(over, answers) ? new TakenOver(operation, source) : null;
        }

        /**
         * How many values {@code source} holds, a run no one container holds — or null where it
         * is one container's, whose count is a taking of that container's place.
         *
         * <p>One operation for every count of a run, whatever the containers the occurrences stand
         * in are: what is counted is the occurrences, which the run holds as a list, so a count
         * written with {@code Set.size} of each set and one written with {@code List.length} of
         * each list are one number and one term.
         *
         * @param each what stands at the place the run's values are read from
         */
        public static TakenOver howManyOf(RunSource source, Type each, NewtypeInners inners,
                                          Symbols symbols) {
            return of(LENGTH, source, each, inners, symbols);
        }

        private static final ValueName.Stdlib.Operation LENGTH =
                ValueName.Stdlib.operation("List", "length");

        public ValueName.Stdlib operation() {
            return operation;
        }

        public RunSource source() {
            return source;
        }

        /** The same taking, over the run read from where {@code moved} puts this one's — or null
         *  where what stands there is no one run, as a run inside an element of another container
         *  is not. */
        @Override
        public TakenOver movedTo(PlacesMoved moved) {
            RunSource at = source.movedTo(moved);
            return at == null ? null : new TakenOver(operation, at);
        }

        /**
         * The same taking over the values at {@code other}, which are values of the type this one's
         * run holds: the account the operation declares was put to that type when this one was
         * made, so it is not asked again.
         */
        TakenOver over(RunSource other) {
            return new TakenOver(operation, Objects.requireNonNull(other, "taken over a run"));
        }

        /** What this operation takes of what it is given. Never null: one of these cannot be made
         *  for an operation that declares none. */
        public TakenAs takenAs() {
            return DefaultBoundOperationFacts.get().takenAs(operation);
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
            return hash;
        }

        @Override
        public TermPath subjectPath() {
            return source.subjectPath();
        }

        @Override
        public String toString() {
            return operation.qualified() + "(" + source + ")";
        }
    }

    /**
     * What two forms of the input's numbers come to multiplied: {@code a * b}, or
     * {@code g * (1 - r)}, each factor a sum of numbers at their weights and a constant.
     *
     * <p>A number of its own and no form over its factors. Fixing every number of one factor
     * leaves a form over the other, weighed by what the first comes to, so a rule about the
     * product relates the numbers of the two factors and divides none of them by a line of its own.
     * The numbers of the two factors are apart ({@link #sharesAPlaceWith}), which is what lets each
     * factor be fixed while the other is chosen: a number read off a place both factors read is
     * not one of these. {@code g - g * r} is {@code g * (1 - r)} here, and it is the reading that
     * brings it to that form; what a run works out is worked out as it was written, and is told of
     * by the operations of the comparison and not by this.
     *
     * <p>The factors in one order whichever was written first, so {@code r * g} is
     * {@code g * r}.
     */
    final class ProductOf implements NumericTerm {

        private final LinearForm<NumericTerm> one;
        private final LinearForm<NumericTerm> other;
        /** Where the number of the factor beside the one alone stands to hold the product at a
         *  value, or null where it stands where that factor is one. */
        private final ExactRatio fixedAt;

        private ProductOf(LinearForm<NumericTerm> one, LinearForm<NumericTerm> other,
                          ExactRatio fixedAt) {
            this.one = one;
            this.other = other;
            this.fixedAt = fixedAt;
        }

        /**
         * The product of {@code left} and {@code right}, or null where either is a constant (that
         * is a form, scaled), or where a number of one is read off a place a number of the other
         * is read off, so that the two are not apart.
         */
        public static ProductOf of(LinearForm<NumericTerm> left, LinearForm<NumericTerm> right) {
            Signed made = signed(left, right);
            return made == null ? null : made.product();
        }

        /**
         * A product and the sign the product of the two forms given is, as the product is
         * written: {@code (1 - r) * g} and {@code (r - 1) * g} are one product, and one is the
         * other negated.
         *
         * @param product the product, each factor turned until its first number is weighed above
         *                nought
         * @param sign    one, or minus one where the forms given were turned to bring it about —
         *                what the product given comes to is {@code sign} times {@code product}
         */
        public record Signed(ProductOf product, ExactRatio sign) {

            /** The product as a form, weighed by its sign. */
            public LinearForm<NumericTerm> asAForm() {
                return new LinearForm<>(ExactRatio.ZERO, Map.of(product, sign));
            }
        }

        /**
         * The product of {@code left} and {@code right} and its sign, or null where the product
         * is none ({@link #of}).
         */
        public static Signed signed(LinearForm<NumericTerm> left, LinearForm<NumericTerm> right) {
            if (left == null || right == null || left.coefs().isEmpty()
                    || right.coefs().isEmpty()) {
                return null;
            }
            for (NumericTerm in : left.coefs().keySet()) {
                for (NumericTerm there : right.coefs().keySet()) {
                    if (in.sharesAPlaceWith(there)) {
                        return null;
                    }
                }
            }
            ExactRatio sign = ExactRatio.ONE;
            LinearForm<NumericTerm> first = turnedUp(left);
            LinearForm<NumericTerm> second = turnedUp(right);
            if (first != left) {
                sign = sign.negated();
            }
            if (second != right) {
                sign = sign.negated();
            }
            boolean firstFirst = String.valueOf(first).compareTo(String.valueOf(second)) <= 0;
            return new Signed(firstFirst ? new ProductOf(first, second, null)
                    : new ProductOf(second, first, null), sign);
        }

        /**
         * {@code form}, or its negation where its constant is below nought — or, where it has
         * none, where its first number, in the order numbers are kept in, is weighed below
         * nought.
         *
         * <p>The constant first, so that {@code 1 - r} stays as it is written and {@code r - 1}
         * is turned to it: the number that makes the form one is nought for the first and two for
         * the second, and a row held at the value of a product by the first multiplies by nought
         * where the second multiplies by two.
         */
        private static LinearForm<NumericTerm> turnedUp(LinearForm<NumericTerm> form) {
            NumericTerm first = NumericTerms.inOrder(form.coefs().keySet()).getFirst();
            if (form.constant().signum() > 0
                    || (form.constant().signum() == 0 && form.coefs().get(first).signum() >= 0)) {
                return form;
            }
            Map<NumericTerm, ExactRatio> negated = new LinkedHashMap<>();
            form.coefs().forEach((term, weight) -> negated.put(term, weight.negated()));
            return new LinearForm<>(form.constant().negated(), negated);
        }

        /** The factor first in the order of factors. */
        public LinearForm<NumericTerm> one() {
            return one;
        }

        /** The other factor. */
        public LinearForm<NumericTerm> other() {
            return other;
        }

        /** Both factors, in their order. */
        public List<LinearForm<NumericTerm>> factors() {
            return List.of(one, other);
        }

        /**
         * How a row comes to hold a given value of the product: one factor is a number alone, and
         * stands at the value; the other is a form of one number, which stands at the number that
         * makes the form one. The product is then the value, and the two numbers are apart.
         *
         * @param carrier the number alone that stands at the value
         * @param fixed   the number of the other factor
         * @param at      where {@code fixed} stands, so that the other factor comes to
         *                {@code scale}
         * @param scale   what the other factor comes to there: one unless the declarations leave
         *                the number no place it is one at, and then the carrier stands at the
         *                value over this
         */
        public record AtAValue(NumericTerm carrier, NumericTerm fixed, ExactRatio at,
                               ExactRatio scale) {}

        /**
         * What the declarations leave the numbers of a product, asked where the place a number
         * stands at is chosen ({@link #standingWhereTheDeclarationsAdmit}).
         */
        public interface Declared {

            /** The values the declarations leave {@code number}, or null where that is not
             *  shown. */
            NumericDomain.Bounds runOf(NumericTerm number);

            /** Whether {@code number} is counted on decimals, whose every value between its
             *  ends is one it can take. */
            boolean isDense(NumericTerm number);
        }

        /**
         * The same product, with the number beside the one alone standing inside the run the
         * declarations leave it where it cannot stand at the value that makes its factor one —
         * and this product where it can, or where no value inside is found.
         *
         * <p>Only where the number alone is counted on decimals: it then stands at the value
         * over what the factor beside comes to, and takes every value that is held. The product
         * is held at a value by one pair of numbers either way, so what reads it and what writes
         * it agree.
         */
        public ProductOf standingWhereTheDeclarationsAdmit(Declared declared) {
            AtAValue way = fixedAt == null ? atAValue() : null;
            if (way == null || !declared.isDense(way.carrier())) {
                return this;
            }
            NumericDomain.Bounds run = declared.runOf(way.fixed());
            if (run == null || run.admits(way.at())) {
                return this;
            }
            ExactRatio inside = insideOf(run);
            ProductOf there = inside == null ? null : new ProductOf(one, other, inside);
            return there == null || there.atAValue() == null ? this : there;
        }

        /** A value inside {@code run}, written as a decimal, nearest its middle; null where none
         *  is found. */
        private static ExactRatio insideOf(NumericDomain.Bounds run) {
            ExactRatio low = run.min() != null && run.min().at() instanceof Count from
                    ? from.exactly() : null;
            ExactRatio high = run.max() != null && run.max().at() instanceof Count to
                    ? to.exactly() : null;
            ExactRatio inside;
            if (low != null && high != null) {
                inside = low.plus(high).flatMap(sum -> sum.dividedBy(ExactRatio.of(2))).orNull();
            } else if (low != null) {
                inside = low.plus(ExactRatio.ONE).orNull();
            } else if (high != null) {
                inside = high.minus(ExactRatio.ONE).orNull();
            } else {
                inside = null;
            }
            return inside != null && run.admits(inside)
                    && Count.written(inside) instanceof ExactAnswer.Held<Optional<Count>>(
                            Optional<Count> written) && written.isPresent() ? inside : null;
        }

        /**
         * The way a given value of this product is held, or null where neither factor is a number
         * alone beside a form of one number that can be made one. The first factor that is a number
         * alone is the one that carries the value.
         */
        public AtAValue atAValue() {
            for (int at = 0; at < 2; at++) {
                LinearForm<NumericTerm> alone = factors().get(at);
                LinearForm<NumericTerm> beside = factors().get(1 - at);
                if (alone.coefs().size() != 1 || !alone.constant().isZero()
                        || !ExactRatio.ONE.equals(alone.coefs().values().iterator().next())
                        || beside.coefs().size() != 1) {
                    continue;
                }
                Map.Entry<NumericTerm, ExactRatio> number =
                        beside.coefs().entrySet().iterator().next();
                if (number.getValue().isZero()) {
                    continue;
                }
                ExactRatio standsAt = fixedAt != null ? fixedAt
                        : ExactRatio.ONE.minus(beside.constant())
                                .flatMap(left -> left.dividedBy(number.getValue())).orNull();
                ExactRatio scale = standsAt == null ? null
                        : fixedAt == null ? ExactRatio.ONE
                        : number.getValue().times(standsAt).flatMap(beside.constant()::plus)
                                .orNull();
                if (standsAt != null && scale != null && !scale.isZero()) {
                    return new AtAValue(alone.coefs().keySet().iterator().next(), number.getKey(),
                            standsAt, scale);
                }
            }
            return null;
        }

        /** Where the first number of the first factor is read from, which is where a reader is
         *  sent and no place the product stands at. */
        @Override
        public TermPath subjectPath() {
            return one.coefs().keySet().iterator().next().subjectPath();
        }

        /** The same product of the numbers read from where {@code moved} puts each — or null
         *  where one of them is no number there, or the two are no longer apart. */
        @Override
        public ProductOf movedTo(PlacesMoved moved) {
            LinearForm<NumericTerm> first = movedForm(one, moved);
            LinearForm<NumericTerm> second = movedForm(other, moved);
            return first == null || second == null ? null : of(first, second);
        }

        private static LinearForm<NumericTerm> movedForm(LinearForm<NumericTerm> form,
                                                         PlacesMoved moved) {
            Map<NumericTerm, ExactRatio> out = new LinkedHashMap<>();
            for (Map.Entry<NumericTerm, ExactRatio> each : form.coefs().entrySet()) {
                NumericTerm there = each.getKey().movedTo(moved);
                if (there == null || out.put(there, each.getValue()) != null) {
                    return null;
                }
            }
            return new LinearForm<>(form.constant(), out);
        }

        @Override
        public boolean equals(Object that) {
            return that instanceof ProductOf product && one.equals(product.one)
                    && other.equals(product.other) && Objects.equals(fixedAt, product.fixedAt);
        }

        @Override
        public int hashCode() {
            return Objects.hash(ProductOf.class, one, other, fixedAt);
        }

        @Override
        public String toString() {
            return written(one) + " * " + written(other);
        }

        /** A factor as an author writes it: a number alone as it is, a sum of them in brackets. */
        private static String written(LinearForm<NumericTerm> factor) {
            if (factor.constant().isZero() && factor.coefs().size() == 1
                    && ExactRatio.ONE.equals(factor.coefs().values().iterator().next())) {
                return factor.coefs().keySet().iterator().next().toString();
            }
            List<String> parts = new ArrayList<>();
            if (!factor.constant().isZero()) {
                parts.add(factor.constant().toString());
            }
            factor.coefs().forEach((number, weight) ->
                    parts.add(ExactRatio.ONE.equals(weight) ? number.toString()
                            : weight + " * " + number));
            return "(" + String.join(" + ", parts) + ")";
        }
    }

    /**
     * Where the subject of this number is read or reported from.
     *
     * <p>Not a position at which this term may be divided. What a reader may do with this is go and
     * look — read the values, ask what the declarations put there, send an author to it — and none
     * of those is drawing a line. A term whose values come from a run of a container answers here as
     * readily as one answered by a single place, and only the second of them has a position a class
     * can be a class of ({@link FromOnePosition#position}).
     *
     * <p>Never the identity of the term either: two terms can be read from one location, and
     * reading one as the other is what this type exists to stop.
     */
    TermPath subjectPath();

    /**
     * The same number, of the value standing where {@code moved} puts each place it is read from —
     * or null where that is no such number. What a behavior states of a number of its parameter is
     * what it states of the same number of whatever a call handed that parameter.
     *
     * <p>The move puts every place somewhere ({@link PlacesMoved}); that the number is none where
     * they are put is this answer's to say, and only this one's.
     */
    NumericTerm movedTo(PlacesMoved moved);

    /**
     * Whether {@code selection}, which keeps some of the occurrences a number is of, is the same
     * selection where {@code moved} puts the places it reads — every one of them handed to the
     * move, as every place a number is read off is ({@link #placesReadOff}), and each left where
     * it is. A selection is null where every occurrence is kept, and is the same anywhere.
     *
     * <p>A statement names places of the input it was read in, and nothing moves one: the number
     * is that number under a move leaving its places where they stand, and no number under one
     * taking them elsewhere.
     */
    static boolean selectionStays(KeptOccurrences selection, PlacesMoved moved) {
        if (selection == null) {
            return true;
        }
        boolean stays = true;
        for (TermPath read : selection.placesRead()) {
            stays &= moved.leaves(read);
        }
        return stays;
    }

    /**
     * Every place this number is read off: each place {@link #movedTo} hands the move, which is
     * every place there is to move, so the two cannot come to name different places.
     */
    default List<TermPath> placesReadOff() {
        List<TermPath> places = new ArrayList<>();
        if (movedTo(PlacesMoved.by(at -> {
            places.add(at);
            return at;
        })) == null) {
            throw new IllegalStateException(this + " moved nowhere is no number, and is one");
        }
        return List.copyOf(places);
    }

    /**
     * Whether this number and {@code other} are read off a place in common, or one is read off a
     * place inside a place the other is.
     *
     * <p>What two numbers being apart comes to, asked of every place each is read off and not of
     * the place a report files it under ({@link #subjectPath}): a count of the times a value
     * occurs in a run is read off the run and off the value, and moves with a number read off the
     * value alone. Two numbers are different for being read by different operations, and are
     * apart only when this is false.
     */
    default boolean sharesAPlaceWith(NumericTerm other) {
        for (TermPath here : placesReadOff()) {
            for (TermPath there : other.placesReadOff()) {
                if (here.isAtOrUnder(there) || there.isAtOrUnder(here)) {
                    return true;
                }
            }
        }
        return false;
    }

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
            // And a product is made of the numbers of two forms, so no one place answers it.
            case ProductOf _ -> null;
            // And a number of an element read off its neighbours is read off all of them, so no
            // value standing at one place is it.
            case OfAnElementsNeighbours _ -> null;
            // Counted among the values of every occurrence, so no one place answers it either.
            case OccurrencesOfItsValue _ -> null;
            case OccurrencesOfAKey _ -> null;
            // Gathered from every element of one key, so from no one place.
            case GatheredUnderItsKey _, GatheredUnderAKey _ -> null;
        };
    }

    /**
     * Whether a line on this number parts the values of no place it is read from.
     *
     * <p>A total of a run is one number that many splits among the elements come to: sixty and
     * forty are on the boundary of a hundred as surely as one hundred is, so a line on the total
     * is a class of no element. A count of how often a value occurs, or the extreme of a key's
     * values, is read off the elements beside one and picks out elements by what they hold, so a
     * line on it is a class of elements though no single place can be asked for it.
     *
     * <p>Exhaustive over the terms there are, with no {@code default}, as {@link #atOnePosition}
     * is: a kind added is one this is answered for.
     */
    default boolean partsNoPlaceByALine() {
        return switch (this) {
            case TakenOver _, ProductOf _ -> true;
            case FromOnePosition _, OfAnElementsNeighbours _, OccurrencesOfItsValue _,
                 OccurrencesOfAKey _, GatheredUnderItsKey _, GatheredUnderAKey _ -> false;
        };
    }

    /**
     * Which number of what stands at {@link #subjectPath} this is, as a place and a kind of number
     * name it — or null where they do not say which number it is.
     *
     * <p>The one answer to it. A number is named by a place where the place and the kind of
     * number say it apart from every other, which is how a clause of a declaration and a statement
     * of a body come to be about one number. Where they do not, a name made of them would be one
     * name for several numbers: the totals of {@code q + 1} and of {@code q + 2} over one list are
     * both a total at the list's elements, and the sums of two containers in every node of a tree
     * are both a sum at its root. Such a number is named by the term itself, which is equal by
     * everything that makes it the number it is.
     *
     * <p>By the operation, and not by something having been taken at the place: a count of a
     * string and the magnitude of a number at one place are two numbers, and one name for both
     * would read a guard on one against the clauses written about the other.
     *
     * <p>Exhaustive over the terms there are, with no {@code default}: a kind added says which of
     * the two it is here, and every reader that names a number asks this.
     */
    default NumberAt.OfWhatNumber atItsPlace() {
        return switch (this) {
            case ValueOf _ -> new NumberAt.OfWhatNumber.OfItsOwnValue();
            case TakenOf taken -> new NumberAt.OfWhatNumber.OfWhatAnOperationAnswers(
                    taken.operation(), taken.arguments(), taken.transformation());
            case CodePointClassCount count ->
                    new NumberAt.OfWhatNumber.OfHowManyCodePointsAreIn(count.counted(),
                            count.through());
            case CodePointValueSum _ -> new NumberAt.OfWhatNumber.OfWhatItsCodePointsComeTo();
            case CodePointAt at -> new NumberAt.OfWhatNumber.OfTheCodePointAt(at.index());
            case WholeUnitsOf units ->
                    new NumberAt.OfWhatNumber.OfTheWholeUnitsOf(units.operation());
            case Multiplicity _ -> new NumberAt.OfWhatNumber.OfItsMultiplicity();
            case OccurrencesOfItsValue occurrences ->
                    new NumberAt.OfWhatNumber.OfItsOccurrencesInEveryContainer(
                            occurrences.selection() == null ? null
                                    : occurrences.selection().key());
            // The key by the whole place it stands at: what a rule calls a place is relative to the
            // value it is a position of, and two parameters are both called the value.
            case OccurrencesOfAKey asked ->
                    new NumberAt.OfWhatNumber.OfTheOccurrencesOfAKey(asked.key().discriminated());
            case ExtremeOfItsKey extreme -> new NumberAt.OfWhatNumber.OfTheExtremeOfItsKey(
                    extreme.extreme(), extreme.keyField().fields(), extreme.through());
            // The operation and the values at the place, where the values are what stands there.
            // What a walk computed of each element, and which nodes of a tree a container is read
            // in, are not said by the place the run is read from.
            case TakenOver over -> switch (over.source()) {
                case RunSource.ProjectedOccurrences _, RunSource.FlattenedOccurrences _ ->
                        new NumberAt.OfWhatNumber.OfWhatAnOperationAnswers(over.operation(),
                                TakenArguments.NONE, ValueTransformation.NONE);
                case RunSource.ComputedOccurrences _, RunSource.ReachableNodes _,
                     RunSource.JoinedOccurrences _ -> null;
            };
            // What each element contributes is a number made of it, which the place does not say
            // even where it reads one field: the field read as another kind of number is another
            // number at the same place.
            case GatheredUnderItsKey _, GatheredUnderAKey _ -> null;
            // Made of the numbers of two forms, which no place and kind of number say apart from
            // another product: it is named by the term itself.
            case ProductOf _ -> null;
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
    default NumericTerm movedTo(TermPath other, Type at, NewtypeInners inners, Symbols symbols) {
        return switch (this) {
            case ValueOf _ -> new ValueOf(other);
            // With what it was given beside the value, which is part of which number it is: a
            // quotient is the one its divisor says, and a taking given none is no quotient.
            case TakenOf taken -> TakenOf.of(taken.operation(),
                    new ObservationSource(other, taken.transformation()), taken.arguments(), at,
                    inners, symbols);
            case CodePointClassCount count ->
                    CodePointClassCount.of(other, count.counted(), count.through(), at, inners);
            case CodePointValueSum _ -> CodePointValueSum.of(other, at, inners);
            case CodePointAt point -> CodePointAt.of(other, point.index(), at, inners);
            // The value it counts is of the type the operation counts, which is all that moving
            // asks: the order it is counted on was settled when the term was made.
            case WholeUnitsOf units -> at != null && DefaultBoundOperationFacts.get()
                    .wholeUnitsCountedOn(units.operation()).equals(TypeOps.base(at, inners))
                    ? new WholeUnitsOf(units.operation(), other, units.image, units.fills) : null;
            // What moves here is where a number is taken, and a run is not taken anywhere: its
            // values come from a place inside a container, and the name that would move is the
            // container's. Answered as "not there" rather than by rebuilding the run at a
            // location, which would be this reading inventing where a walk got its values.
            case TakenOver _ -> null;
            // A number of an element read off its neighbours is read off the container it stands
            // in, so a place moved alone is a number of some other container's elements.
            case OfAnElementsNeighbours _ -> null;
            // Counted among every occurrence of a place, so a place moved alone is another run.
            case OccurrencesOfItsValue _ -> null;
            // The same, and the key it counts for is another place a moved place leaves behind.
            case OccurrencesOfAKey _ -> null;
            // Gathered over a run, which a place moved alone is another one of.
            case GatheredUnderItsKey _, GatheredUnderAKey _ -> null;
            // Made of places, and a place moved alone is one factor's of the two.
            case ProductOf _ -> null;
        };
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
     * <p>A taking is read with what it was given beside the value, which is what a bound stated
     * under a divisor reads: a remainder by seven lies from nought up to seven, and by an unknown
     * divisor lies nowhere in particular. A taking over a run carries none, because what a total is
     * taken of is a container, and an operation like that declares no row that names one.
     */
    default NumericDomain.Bounds intrinsicBounds() {
        return switch (this) {
            case ValueOf _ -> NumericDomain.Bounds.OPEN;
            // And what the value it was taken of can be: a date moved a year's days back is never
            // the last date, so its year is never the last year, whatever the operation answers of
            // any date.
            case TakenOf taken -> taken.whatTheOperationStates()
                    .meet(taken.takenAs().reachedFrom(taken.transformation()));
            // A count of some of a string's code points is never negative, as how many it holds is
            // not. What it is at most is the string's own length, which is another number of the
            // same place and is held where the two are realized together.
            case CodePointClassCount _ ->
                    new NumericDomain.Bounds(Endpoint.inclusive(Count.of(0)), null);
            // No code point is below nought, so neither is what they come to, and a string of
            // none comes to nought.
            case CodePointValueSum _ ->
                    new NumericDomain.Bounds(Endpoint.inclusive(Count.of(0)), null);
            // A scalar value, which is from nought to the last there is.
            case CodePointAt _ -> new NumericDomain.Bounds(Endpoint.inclusive(Count.of(0)),
                    Endpoint.inclusive(Count.of(Character.MAX_CODE_POINT)));
            // The steps some value of the position's type falls in, which is all of the answer's
            // order or a part of it, and open where that was not worked out.
            case WholeUnitsOf steps -> steps.image == null ? NumericDomain.Bounds.OPEN
                    : steps.image;
            // An element is one of the elements it counts, so there is always at least one.
            case Multiplicity _ ->
                    new NumericDomain.Bounds(Endpoint.inclusive(Count.of(1)), null);
            // The same: a value is one of the values it counts.
            case OccurrencesOfItsValue _ ->
                    new NumericDomain.Bounds(Endpoint.inclusive(Count.of(1)), null);
            // None of the values may be the key's, so the count starts at nought.
            case OccurrencesOfAKey _ ->
                    new NumericDomain.Bounds(Endpoint.inclusive(Count.of(0)), null);
            // One of the values the place holds, which is open where the place is.
            case ExtremeOfItsKey _ -> NumericDomain.Bounds.OPEN;
            // An end is one of the numbers of its key and a total any number they add up to; what
            // they are bounded by is what the elements' rules guarantee, which is a reading of
            // the run and not of the term.
            case GatheredUnderItsKey _, GatheredUnderAKey _ -> NumericDomain.Bounds.OPEN;
            // What two forms come to multiplied is not bounded by the form of either alone.
            case ProductOf _ -> NumericDomain.Bounds.OPEN;
            // Asked of the operation, as a taking is. That a total of non-negative amounts is
            // itself non-negative is not among the answers: it follows from what the values the run
            // walks guarantee, together with the value the operation starts from and the step it
            // repeats. That is a statement about the run and not about the operation, and it is the
            // run's own reading to make. Declared here as a range of the operation, it would be
            // wrong for a run whose elements may be negative.
            case TakenOver over -> ResultRange.of(
                    DefaultBoundOperationFacts.get().boundsOnTheResult(over.operation()),
                    ConstantArguments.none());
        };
    }

    /**
     * What this term's values can be: {@link #intrinsicBounds} and what the language can hold
     * ({@link RepresentationBounds}).
     *
     * <p>For asking whether a value can stand, and by {@link RepresentationBounds#ofAForm} to weigh
     * several terms. Not for what a position is divided into: its classes and the ends of its runs
     * are {@link #intrinsicBounds}, since the longest string is no distinction a model made.
     */
    default NumericDomain.Bounds reachBounds() {
        return intrinsicBounds().meet(RepresentationBounds.of(this));
    }

    /** Whether {@code place} is reached from an element of {@code container} by fields alone, and
     *  so is one value of each element. */
    private static boolean fieldsBelowAnElement(TermPath container, TermPath place) {
        if (!place.isAtOrUnder(container.element())) {
            return false;
        }
        List<TermPath.Step> steps = place.steps();
        return steps.subList(container.element().steps().size(), steps.size()).stream()
                .allMatch(TermPath.Step.Field.class::isInstance);
    }

    /** The way from an element of {@code container} to {@code place}, which
     *  {@link #fieldsBelowAnElement} has said is fields alone. */
    private static ElementProjection fieldsTo(TermPath container, TermPath place) {
        return ElementProjection.below(container.element(), place);
    }

    /**
     * The count at a value, keeping why there is none where there is none.
     *
     * <p><b>At a value, which a reading of one always has.</b> Whether a walk arrived and what it
     * found are settled before a term is asked, so nothing here stands for a place nobody reached
     * or a position a row wrote nothing at — those are said where they happen, in the words their
     * own layer has for them. An arm for them here would be a word that means none of them and
     * takes all of them, which is what a reader downstream then has to unpick.
     */
    sealed interface Reading {

        record Number(Place value) implements Reading {}

        /**
         * A value was there and the observation of it did not come back whole.
         *
         * <p>What {@link Incompleteness.Code} names is what an observation met, so only an
         * observation may put one here. A walk that arrived at no value at all has met nothing and
         * never reaches this type: given a code instead, the nearest one is borrowed, and a reader
         * downstream that words a code as what an observation did then says an observation did
         * something that never happened.
         *
         * <p>With the figure it stopped at where a limit stopped it, which only the observation
         * knows and a reader that says a limit stopped it names.
         */
        record Missing(Incompleteness.Cause cause) implements Reading {

            public Missing {
                if (cause == null) {
                    throw new IllegalArgumentException("an observation that did not come back"
                            + " whole says what it met");
                }
            }

            /** What the observation met, as the word it writes for it. */
            public Incompleteness.Code code() {
                return cause.code();
            }
        }

        /** The value was read and this term is not a number of it. An answer about the value and not
         * about the observation: a {@code Text} where a number was expected is a class nothing holds,
         * and calling it unreadable would report a partition that does not fit its position as a row
         * nobody could read. */
        record NotNumber() implements Reading {}

        /**
         * Every value the term reads arrived, and the number they come to is one the exact
         * arithmetic could not hold.
         *
         * <p>Not {@link NotNumber}: the values are there and are numbers, and what stopped is this
         * compiler working out how far apart they stand — the same fact {@link Missing} cannot carry
         * either, since nothing here is an observation that came back short. A reader that folded
         * this into either would tell a caller the term definitely is not a number of the value, or
         * that a value was there and unread, neither of which is what happened.
         */
        record NotWorkedOut(UnheldNumber why) implements Reading {

            public NotWorkedOut {
                if (why == null) {
                    throw new IllegalArgumentException(
                            "a number not worked out says why it was not");
                }
            }
        }
    }
}
