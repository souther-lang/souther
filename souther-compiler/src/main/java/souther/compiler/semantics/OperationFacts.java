package souther.compiler.semantics;

import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Rel;
import souther.compiler.types.BinOp;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;

/**
 * What is true of the language's own operations, as somebody wrote it down.
 *
 * <p>The declarations are the list, and the list is the whole of what this publishes. A fact is
 * written here in the authoring vocabulary — a name for the operation, a word for an argument —
 * and nothing here says the library has such an operation or such an argument. Holding every one
 * of these to the library's own declarations reads signatures, which is the frontend's; it happens
 * once over the whole list ({@code check.OperationFactBinder}), and what comes out of that walk is
 * a value of another kind, in which every name has been read against its declaration
 * ({@code check.BoundOperationFacts}). Every reader of a fact reads that one.
 *
 * <p><b>No lookup here, by design.</b> An index keyed by operation and read off this list would be
 * a way to a fact that does not pass through the binding, and a reader that took it would be
 * holding the authored word and putting the binder's question a second time — with an answer that
 * agrees with the binder's for exactly as long as nobody changes either. So this list is read by
 * one caller, and a reader that wants a fact asks what the binding made of it.
 */
public final class OperationFacts {

    /** One fact, and the operation it is about. */
    public record Declared(ValueName operation, OperationFact fact) {

        public Declared {
            java.util.Objects.requireNonNull(operation, "a fact is about an operation");
            java.util.Objects.requireNonNull(fact, "and says something");
        }
    }

    private static Declared about(String alias, String name, OperationFact fact) {
        return new Declared(op(alias, name), fact);
    }

    /** The argument at {@code position}, for a fact whose operation's signature does not say which
     *  one it is about. */
    private static ArgumentRef at(int position) {
        return new ArgumentRef.At(position);
    }

    /** The argument the signature already says the elements come from, where the operation takes a
     *  closure at all — so a fact about such an operation writes no position of its own. */
    private static final ArgumentRef CONTAINER = new ArgumentRef.TheContainer();

    /**
     * Everything declared here.
     *
     * <p>One list and not one per kind. What holds these to the library reads this, so a kind added
     * beside it would be a kind nothing validates until someone remembers — and the arrangement is
     * meant to make remembering unnecessary.
     */
    private static final List<Declared> DECLARED = declared();

    private static List<Declared> declared() {
        return List.of(
            // What each answers, counted, in what its arguments are counted as. A date's count is
            // its carrier's, so a difference of two of them is a number of days while neither is a
            // number — which is the whole of why these can be said at all.
            about("Decimal", "fromInt", answers(form(at(0), 1))),
            about("Date", "daysBetween", answers(form(at(0), -1).plus(form(at(1), 1)))),
            about("Date", "addDays", answers(form(at(0), 1).plus(form(at(1), 1)))),
            // The same over the second the date-times count, which is the epoch second a local
            // value stands at: a day is eighty-six thousand four hundred of them, exactly, because
            // the value carries no zone for anything to shift it by.
            about("DateTime", "addMinutes", answers(form(at(0), 60).plus(form(at(1), 1)))),
            about("DateTime", "addHours", answers(form(at(0), 3600).plus(form(at(1), 1)))),
            about("DateTime", "addDays", answers(form(at(0), 86400).plus(form(at(1), 1)))),
            // And the one that puts two counts together: a date counts days from the epoch and a
            // time counts seconds into its day, so the date-time they make counts the first at a
            // day's worth of seconds and the second as it stands.
            about("DateTime", "fromDateAndTime",
                    answers(form(at(0), 86400).plus(form(at(1), 1)))),

            // The operations whose result is a number taken of the one value they are given, and
            // what each takes of it. The arm is the whole of what is said here: where the number
            // runs is declared below with the other bounds, and what it is measured by is the
            // operation's own result type.
            about("List", "length", takenAs(new TakenAs.HowManyItHolds())),
            about("String", "length", takenAs(new TakenAs.HowManyItHolds())),
            about("Set", "size", takenAs(new TakenAs.HowManyItHolds())),
            about("Map", "size", takenAs(new TakenAs.HowManyItHolds())),
            // `Int.abs` and `Decimal.abs` are not here and cannot be. They are ordinary `let`s over
            // `<` and `-`, so a body reading expands them and reads the comparison inside; a term
            // standing for the call would be a second reading of the same call, which is what the
            // exclusivity below refuses.
            about("Time", "hour", takenAs(new TakenAs.PartOfTime(TakenAs.TimePart.HOUR))),
            about("Time", "minute", takenAs(new TakenAs.PartOfTime(TakenAs.TimePart.MINUTE))),
            about("Time", "second", takenAs(new TakenAs.PartOfTime(TakenAs.TimePart.SECOND))),
            about("Date", "year", takenAs(new TakenAs.PartOfDate(TakenAs.DatePart.YEAR))),
            about("Date", "month", takenAs(new TakenAs.PartOfDate(TakenAs.DatePart.MONTH))),
            about("Date", "day", takenAs(new TakenAs.PartOfDate(TakenAs.DatePart.DAY))),

            // A count is never negative, and each of these says so itself. Derived from the arm
            // instead, the arm would be where a bound is really declared and every operation
            // sharing it would carry the same one — which is what a term saying "a size is never
            // negative" was, one level down (#1027). `everyMeasureAnswersACountThatIsNotNegative`
            // is what holds the four of them to it.
            about("List", "length", bounded(Rel.GE, 0)),
            about("String", "length", bounded(Rel.GE, 0)),
            about("Set", "size", bounded(Rel.GE, 0)),
            about("Map", "size", bounded(Rel.GE, 0)),

            // And the ones every answer of which some value it could be given answers. A string of
            // any length is written by repeating a character; every hour of the day is an hour some
            // time falls in. The counts over an element the language may have none of are not here,
            // and say why where the fact is declared.
            about("String", "length",
                    new OperationFact.EveryAnswerItCanGiveHasASourceValue()),
            about("Time", "hour", new OperationFact.EveryAnswerItCanGiveHasASourceValue()),
            about("Time", "minute", new OperationFact.EveryAnswerItCanGiveHasASourceValue()),
            about("Time", "second", new OperationFact.EveryAnswerItCanGiveHasASourceValue()),
            about("Date", "year", new OperationFact.EveryAnswerItCanGiveHasASourceValue()),
            about("Date", "month", new OperationFact.EveryAnswerItCanGiveHasASourceValue()),
            about("Date", "day", new OperationFact.EveryAnswerItCanGiveHasASourceValue()),

            // What holds of a result wherever the call is written. Each is a fact about the
            // operation, so it is stated at every call and not only where something was guarded:
            // `Int.abs(x)` is not negative whatever `x` is.
            //
            // `Int.floorMod` states both its ends only where the divisor reads as a constant above
            // zero, and neither of them otherwise. The result takes the sign of the divisor —
            // `floorMod(1, -3)` is `-2` — so a divisor that could be negative puts it the other
            // side of zero, and the lower end is as much the divisor's to decide as the upper one.
            // Its `0` is not a case at all: the operation aborts.
            //
            // `Decimal.toInt` is within one of what it rounds, whichever mode it is handed. What a
            // single mode does more narrowly — `HALF_UP` rounds to within a half — is a second
            // statement and is not made here, since the mode is an argument nothing reads.
            about("Int", "abs", bounded(Rel.GE, 0)),
            about("Decimal", "abs", bounded(Rel.GE, 0)),
            about("Int", "floorMod", bounded(Rel.GE, 0, aboveZero(at(1)))),
            about("Int", "floorMod", bounded(Rel.LT, at(1), 0, aboveZero(at(1)))),
            about("Decimal", "toInt", bounded(Rel.GT, at(1), -1, always())),
            about("Decimal", "toInt", bounded(Rel.LT, at(1), 1, always())),

            // A comparison answers a sign and answers it as one of three numbers. That it is one of
            // three is not what {@code StatesTheOrderOfItsArguments} says: that one says which
            // argument a positive answer names as the greater, and a comparison answering the
            // difference of the two would say the same thing about the same order. So the ends are
            // stated here, where they are what they are — the number, and not the order it decides.
            about("Int", "compare", bounded(Rel.GE, -1)),
            about("Int", "compare", bounded(Rel.LE, 1)),
            about("Decimal", "compare", bounded(Rel.GE, -1)),
            about("Decimal", "compare", bounded(Rel.LE, 1)),
            about("Rational", "compare", bounded(Rel.GE, -1)),
            about("Rational", "compare", bounded(Rel.LE, 1)),

            // The parts a temporal is read out in, each within the range that part of a calendar
            // has. A month is one of twelve and a day one of at most thirty-one whatever the date
            // is, so neither is a bound the arguments decide.
            about("Time", "hour", bounded(Rel.GE, 0)),
            about("Time", "hour", bounded(Rel.LE, 23)),
            about("Time", "minute", bounded(Rel.GE, 0)),
            about("Time", "minute", bounded(Rel.LE, 59)),
            about("Time", "second", bounded(Rel.GE, 0)),
            about("Time", "second", bounded(Rel.LE, 59)),
            about("Date", "month", bounded(Rel.GE, 1)),
            about("Date", "month", bounded(Rel.LE, 12)),
            about("Date", "day", bounded(Rel.GE, 1)),
            about("Date", "day", bounded(Rel.LE, 31)),

            // And the two whose ends are where the calendar stops rather than where a part of one
            // does. A year is the year of a date, and a date is written between two of them; a count
            // of minutes is a count between two date-times, and no two of them stand further apart
            // than the first and the last. Both are read off what a value of the type can be rather
            // than written down as numbers here, since what a temporal can be written as is already
            // answered — by {@code java.time} for a date, which is what the carrier's own ends are
            // read from, and by {@link souther.compiler.numeric.DateTimes} for a date-time.
            about("Date", "year", bounded(Rel.GE, java.time.LocalDate.MIN.getYear())),
            about("Date", "year", bounded(Rel.LE, java.time.LocalDate.MAX.getYear())),
            about("DateTime", "minutesBetween", bounded(Rel.GE, -minutesAcrossEveryDateTime())),
            about("DateTime", "minutesBetween", bounded(Rel.LE, minutesAcrossEveryDateTime())),

            // The operations that move a value by an amount, each stated through the measure that
            // counts two such values apart. Every one of them works on a local value, where a day
            // is a day and an hour is sixty minutes, so what each states is exact rather than
            // usually true.
            about("Date", "addDays", shifts("Date", "daysBetween", at(1), at(0), 1)),
            about("DateTime", "addMinutes", shifts("DateTime", "minutesBetween", at(1), at(0), 1)),
            about("DateTime", "addHours", shifts("DateTime", "minutesBetween", at(1), at(0), 60)),
            about("DateTime", "addDays", shifts("DateTime", "minutesBetween", at(1), at(0), 1440)),

            // The operations answering the order of their two arguments as the sign of a number.
            // The direction is not the same for all of them: `compare(a, b)` is positive where `a`
            // is the greater, and `daysBetween(from, to)` counts forward from its first argument.
            about("Int", "compare",
                    new OperationFact.StatesTheOrderOfItsArguments(
                            PositiveOrder.FIRST_ARGUMENT_GREATER)),
            about("Decimal", "compare",
                    new OperationFact.StatesTheOrderOfItsArguments(
                            PositiveOrder.FIRST_ARGUMENT_GREATER)),
            about("Rational", "compare",
                    new OperationFact.StatesTheOrderOfItsArguments(
                            PositiveOrder.FIRST_ARGUMENT_GREATER)),
            about("Date", "daysBetween",
                    new OperationFact.StatesTheOrderOfItsArguments(
                            PositiveOrder.SECOND_ARGUMENT_GREATER)),

            // Where a construction's elements came from, and how many of them it answers.
            about("List", "reverse", keeps(at(0), SizeAgainstItsSource.SAME)),
            about("List", "sort", keeps(at(0), SizeAgainstItsSource.SAME)),
            about("List", "sortBy", keeps(CONTAINER, SizeAgainstItsSource.SAME)),
            about("List", "map", maps(CONTAINER, SizeAgainstItsSource.SAME)),
            about("List", "mapIndexed", maps(CONTAINER, SizeAgainstItsSource.SAME)),
            about("Map", "mapValues", maps(CONTAINER, SizeAgainstItsSource.SAME)),
            about("List", "filter", keeps(CONTAINER, SizeAgainstItsSource.AT_MOST)),
            about("List", "distinct", keeps(at(0), SizeAgainstItsSource.AT_MOST)),
            about("List", "take", keeps(at(1), SizeAgainstItsSource.AT_MOST)),
            about("List", "drop", keeps(at(1), SizeAgainstItsSource.AT_MOST)),
            about("Set", "filter", keeps(CONTAINER, SizeAgainstItsSource.AT_MOST)),
            about("Map", "filterEntries", keeps(CONTAINER, SizeAgainstItsSource.AT_MOST)),
            about("List", "distinctBy", keeps(CONTAINER, SizeAgainstItsSource.AT_MOST)),
            about("Map", "remove", keeps(at(1), SizeAgainstItsSource.AT_MOST)),
            about("Set", "remove", keeps(at(1), SizeAgainstItsSource.AT_MOST)),
            about("Map", "intersection", keeps(at(0), SizeAgainstItsSource.AT_MOST)),
            about("Map", "difference", keeps(at(0), SizeAgainstItsSource.AT_MOST)),
            about("Set", "intersection", keeps(at(0), SizeAgainstItsSource.AT_MOST)),
            about("Set", "difference", keeps(at(0), SizeAgainstItsSource.AT_MOST)),
            // Every value in the answer came from the map it was given: the one under the key is
            // what the closure made of it, and every other is the value that was there. Read as a
            // closure result alone, what is true of one value would be said of all of them.
            about("Map", "updateIfPresent", new OperationFact.BuildsItsResultFrom(new BuiltFrom<>(
                    new ElementLineage.OneOf<>(List.of(
                            new ElementLineage.SameAs<>(new ElementLineage.Source<>(CONTAINER, 1)),
                            new ElementLineage.ClosureResult<>(
                                    new ElementLineage.Source<>(CONTAINER, 1)))),
                    SizeAgainstItsSource.SAME))),
            // Inside what the closure answered, which is an optional here and a list in a
            // `flatMap`. One lineage for the two, told apart by what the closure's own signature
            // says it answers with.
            about("List", "filterMap", new OperationFact.BuildsItsResultFrom(new BuiltFrom<>(
                    new ElementLineage.InsideClosureResult<>(
                            new ElementLineage.Source<>(CONTAINER, 1)), SizeAgainstItsSource.AT_MOST))),
            about("Set", "map", maps(CONTAINER, SizeAgainstItsSource.AT_MOST)),

            // Which side of an answer the closure decides, said and not read off a size. That a
            // filter answers at most as many as it walked is the size fact above; that the
            // closure's truth is why it answers fewer is this one, and a take or a distinct shows
            // they are different statements — both answer at most as many, and neither of those
            // asks a closure anything about it. So the edge is written for the operations whose
            // answer the closure really does decide, and everything else says nothing.
            //
            // A mapping is the case this is for. `List.map` answers one per element whatever the
            // closure said, so a rule written inside it decides what the answers are and not
            // whether there are any.
            //
            // `List.distinctBy` is the case beside it. Its key does change how many it answers —
            // two elements it sends to one key are one element of the answer — and never whether
            // it answers any, since the first element of what it walked is always kept. So it says
            // nothing here: what it decides is the count, and the count is not what a fork on
            // emptiness reads.
            //
            // `List.filterMap` decides emptiness, and by whether the closure answered a value
            // rather than by whether it holds. Nothing here can say that yet, so it says nothing
            // rather than saying the nearest thing.
            about("List", "filter", turnsOn(AnswerAspect.EMPTINESS)),
            about("Set", "filter", turnsOn(AnswerAspect.EMPTINESS)),
            about("Map", "filterEntries", turnsOn(AnswerAspect.EMPTINESS)),
            // And the two whose whole answer is what the closure said of the elements.
            about("List", "any", turnsOn(AnswerAspect.TRUTH)),
            about("List", "all", turnsOn(AnswerAspect.TRUTH)),
            // And a negation, whose whole answer is the truth of what it was given. Not a closure,
            // which is why the fact names an argument rather than one kind of one.
            about("Bool", "not", turnsOn(AnswerAspect.TRUTH, at(0))),

            // The containers a construction's result is never smaller than. A union answers one of
            // what both sides hold and an insert of something already there adds nothing, so
            // neither answers the sum of what it read; appending does, and stating it for that one
            // alone would be a second statement for one operation. The bound is what they share.
            about("List", "append", noSmallerThan(at(0))),
            about("List", "append", noSmallerThan(at(1))),
            about("Set", "union", noSmallerThan(at(0))),
            about("Set", "union", noSmallerThan(at(1))),
            about("Map", "union", noSmallerThan(at(0))),
            about("Map", "union", noSmallerThan(at(1))),
            about("Set", "insert", noSmallerThan(at(1))),
            about("Map", "insert", noSmallerThan(at(2))),

            // The operations that answer what a container holds accumulated, and what walking one
            // comes to. `List.concat` and `String.concat` are here beside the two numeric ones
            // because they are the same shape said of other values: a list of lists joined from the
            // empty list, a list of strings joined from the empty string — which the library states
            // as `join("", xs)` itself.
            //
            // `String.join` is in range and is not one of these. A separator stands between
            // elements and not before the first, so what the walk does at an element depends on
            // whether anything came before it, and an identity with a step over two values of one
            // type has nowhere to keep that.
            about("List", "sum",
                    accumulates(at(0), Accumulation.Identity.ZERO, Accumulation.Combine.ADD)),
            about("List", "product",
                    accumulates(at(0), Accumulation.Identity.ONE, Accumulation.Combine.MULTIPLY)),
            about("List", "concat",
                    accumulates(at(0), Accumulation.Identity.EMPTY, Accumulation.Combine.APPEND)),
            about("String", "concat",
                    accumulates(at(0), Accumulation.Identity.EMPTY, Accumulation.Combine.APPEND)),

            // Where a predicate reads its container, and which shapes of construction carry its
            // statement there.
            about("List", "all", reads(CONTAINER, ElementShape.PERMUTES, ElementShape.SUBSET)),
            about("List", "allDistinctBy",
                    reads(CONTAINER, ElementShape.PERMUTES, ElementShape.SUBSET)),
            about("List", "any", reads(CONTAINER, ElementShape.PERMUTES)),
            about("List", "contains", reads(at(1), ElementShape.PERMUTES)),
            about("Set", "contains", reads(at(1), ElementShape.PERMUTES)),
            about("Map", "containsKey", reads(at(1), ElementShape.PERMUTES)),

            about("List", "allDistinctBy",
                    new OperationFact.IsStatedOverAProjection(new ArgumentRef.TheClosure())),
            about("List", "all", new OperationFact.StatesItsPredicateOfEveryElement()),

            about("List", "isEmpty", meansSizeOf("List", "length")),
            about("Set", "isEmpty", meansSizeOf("Set", "size")),
            about("Map", "isEmpty", meansSizeOf("Map", "size")),
            about("String", "isEmpty", meansSizeOf("String", "length")),

            // Which arithmetic each operation computes, and where it answers it. A division comes
            // back as `DivisionByZero` where its divisor is nought, so the number is in the case
            // carrying it rather than the result itself.
            about("Int", "add", computes(new Arithmetic.TheOperator(BinOp.ADD))),
            about("Int", "subtract", computes(new Arithmetic.TheOperator(BinOp.SUB))),
            about("Int", "multiply", computes(new Arithmetic.TheOperator(BinOp.MUL))),
            about("Decimal", "add", computes(new Arithmetic.TheOperator(BinOp.ADD))),
            about("Decimal", "subtract", computes(new Arithmetic.TheOperator(BinOp.SUB))),
            about("Decimal", "multiply", computes(new Arithmetic.TheOperator(BinOp.MUL))),
            about("Int", "truncatingDivide",
                    computesInTheCaseCarrying(Type.INT, new Arithmetic.ATruncatingQuotient())),
            about("Int", "truncatingRemainder",
                    computesInTheCaseCarrying(Type.INT, new Arithmetic.ATruncatingRemainder())),
            about("Decimal", "divide",
                    computesInTheCaseCarrying(Type.DECIMAL,
                            new Arithmetic.AQuotientRoundedToAScale())),

            // The operations that answer one of the values they were given, as the cases their
            // definitions are written in.
            about("Int", "min", answers(at(0), stands(at(0), Rel.LT, at(1)))),
            about("Int", "min", answers(at(1), stands(at(0), Rel.GE, at(1)))),
            about("Decimal", "min", answers(at(0), stands(at(0), Rel.LT, at(1)))),
            about("Decimal", "min", answers(at(1), stands(at(0), Rel.GE, at(1)))),
            about("Int", "max", answers(at(0), stands(at(0), Rel.GT, at(1)))),
            about("Int", "max", answers(at(1), stands(at(0), Rel.LE, at(1)))),
            about("Decimal", "max", answers(at(0), stands(at(0), Rel.GT, at(1)))),
            about("Decimal", "max", answers(at(1), stands(at(0), Rel.LE, at(1)))),
            about("Int", "clamp", answers(at(0), stands(at(2), Rel.LT, at(0)))),
            about("Int", "clamp", answers(at(1), stands(at(2), Rel.GE, at(0)),
                    stands(at(2), Rel.GT, at(1)))),
            about("Int", "clamp", answers(at(2), stands(at(2), Rel.GE, at(0)),
                    stands(at(2), Rel.LE, at(1)))),
            about("Decimal", "clamp", answers(at(0), stands(at(2), Rel.LT, at(0)))),
            about("Decimal", "clamp", answers(at(1), stands(at(2), Rel.GE, at(0)),
                    stands(at(2), Rel.GT, at(1)))),
            about("Decimal", "clamp", answers(at(2), stands(at(2), Rel.GE, at(0)),
                    stands(at(2), Rel.LE, at(1)))));
    }

    /** How many whole minutes the first date-time and the last stand apart, which is as far apart as
     *  a count of minutes between two of them reaches either way. Read off the counts the carrier
     *  runs between: what a date-time can be written as is answered there, and a number written here
     *  would be a second answer to it. */
    private static long minutesAcrossEveryDateTime() {
        return souther.compiler.numeric.DateTimes.MAX.at()
                .subtract(souther.compiler.numeric.DateTimes.MIN.at())
                .divideToIntegralValue(java.math.BigDecimal.valueOf(60))
                .longValueExact();
    }

    /** The operation {@code name} of the library module published as {@code alias}. Written as the
     *  two values it is, so that a declaration says which library it is about without a reader
     *  splitting a spelling to find out. */
    private static ValueName op(String alias, String name) {
        return ValueName.Stdlib.operation(alias, name);
    }

    private static OperationFact computes(Arithmetic arithmetic) {
        return new OperationFact.ComputesANumber(new NumericResult<>(
                new NumericResult.Answered.Directly(), arithmetic, null));
    }

    /** The condition every division comes back as {@code DivisionByZero} under. */
    private static OperationFact computesInTheCaseCarrying(Type carried, Arithmetic arithmetic) {
        return new OperationFact.ComputesANumber(new NumericResult<>(
                new NumericResult.Answered.InTheCaseCarrying(carried), arithmetic,
                new NumericResult.TheOtherCaseWhen<>(at(1), BinOp.EQ, 0)));
    }

    @SafeVarargs
    private static OperationFact answers(ArgumentRef argument,
                                         ArgumentsStand<ArgumentRef>... given) {
        List<ArgumentsStand<ArgumentRef>> reached = new ArrayList<>(given.length);
        for (ArgumentsStand<ArgumentRef> stands : given) {
            reached.add(stands);
        }
        return new OperationFact.IsDefinedByCases(new DefinitionCase<>(argument, reached));
    }

    private static ArgumentsStand<ArgumentRef> stands(ArgumentRef left, Rel rel,
                                                      ArgumentRef right) {
        return new ArgumentsStand<>(left, rel, right);
    }

    private static OperationFact noSmallerThan(ArgumentRef container) {
        return new OperationFact.ResultIsNoSmallerThan(container);
    }

    private static OperationFact reads(ArgumentRef container, ElementShape... through) {
        return new OperationFact.ReadsItsContainer(container, java.util.Set.of(through));
    }

    private static OperationFact takenAs(TakenAs how) {
        return new OperationFact.AnswersANumberTakenOfAValueItIsGiven(how);
    }

    /** The answer is what {@code container} holds, started from {@code identity} and carried
     *  through {@code combine}. */
    private static OperationFact accumulates(ArgumentRef container,
                                             Accumulation.Identity identity,
                                             Accumulation.Combine combine) {
        return new OperationFact.AccumulatesItsContainer(container,
                new Accumulation(identity, combine));
    }

    private static OperationFact meansSizeOf(String module, String size) {
        return new OperationFact.MeansTheSameAsASizeOfNought(ValueName.Stdlib.operation(module, size));
    }

    /** What an argument decides, for the operations whose answer turns on it. */
    private static OperationFact turnsOn(AnswerAspect aspect) {
        return new OperationFact.TurnsOnWhetherAnArgumentHolds(aspect, new ArgumentRef.TheClosure());
    }

    /** The same, where the argument is not a closure. */
    private static OperationFact turnsOn(AnswerAspect aspect, ArgumentRef argument) {
        return new OperationFact.TurnsOnWhetherAnArgumentHolds(aspect, argument);
    }

    /** The answer holds the very elements {@code source} held. */

    private static OperationFact keeps(ArgumentRef source, SizeAgainstItsSource size) {
        return new OperationFact.BuildsItsResultFrom(new BuiltFrom<>(
                new ElementLineage.SameAs<>(new ElementLineage.Source<>(source, 1)), size));
    }

    /** The answer holds what a closure made of each of {@code source}'s elements. */
    private static OperationFact maps(ArgumentRef source, SizeAgainstItsSource size) {
        return new OperationFact.BuildsItsResultFrom(new BuiltFrom<>(
                new ElementLineage.ClosureResult<>(new ElementLineage.Source<>(source, 1)), size));
    }

    /** {@code times} of what one argument is counted as. */
    private static souther.compiler.numeric.LinearForm<ArgumentRef> form(
            ArgumentRef argument, long times) {
        return souther.compiler.numeric.LinearForm.<ArgumentRef>atom(argument)
                .times(ExactRatio.of(times));
    }

    private static OperationFact answers(
            souther.compiler.numeric.LinearForm<ArgumentRef> form) {
        return new OperationFact.AnswersAFormOfItsArguments(form);
    }

    private static OperationFact bounded(Rel rel, long n) {
        return bounded(rel, null, n, always());
    }

    private static OperationFact bounded(Rel rel, long n,
                                         ResultBound.Provided<ArgumentRef> provided) {
        return bounded(rel, null, n, provided);
    }

    private static OperationFact bounded(Rel rel, ArgumentRef against, long offset,
                                         ResultBound.Provided<ArgumentRef> provided) {
        return new OperationFact.BoundsItsResult(
                new ResultBound<>(against, java.math.BigDecimal.valueOf(offset), rel, provided));
    }

    private static ResultBound.Provided<ArgumentRef> always() {
        return new ResultBound.Provided.Always<>();
    }

    private static ResultBound.Provided<ArgumentRef> aboveZero(ArgumentRef argument) {
        return new ResultBound.Provided.ConstantAboveZero<>(argument);
    }

    private static OperationFact shifts(String module, String measure, ArgumentRef of,
                                        ArgumentRef amount, long per) {
        return new OperationFact.ShiftsBy(ValueName.Stdlib.operation(module, measure), of, amount,
                java.math.BigDecimal.valueOf(per));
    }

    /**
     * Every fact declared, for what holds them to the library's declarations.
     *
     * <p>The one thing this publishes, and read by one caller ({@code check.OperationFactBinder}).
     * A second reader of this list would be a reader of the authoring vocabulary below the
     * binding, which is what {@code OnlyTheBinderReadsTheAuthoringVocabularyTest} counts.
     */
    public static List<Declared> declarations() {
        return DECLARED;
    }

    private OperationFacts() {}
}
