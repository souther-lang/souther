package souther.compiler.semantics;

import souther.compiler.numeric.NumericDomain.Rel;
import souther.compiler.types.BinOp;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * What is true of the language's own operations.
 *
 * <p>The declarations are the list, and everything else here is read off it. An index is derived
 * rather than declared beside the list, so a fact cannot exist without being among the
 * declarations — which is what the procedures that validate these enumerate, and what a fact added
 * later is therefore part of without anyone remembering to add it anywhere.
 *
 * <p><b>Looking one up is a lookup and nothing else.</b> Holding these to the library's own
 * declarations reads signatures, which is the frontend's; it happens once over the whole list
 * ({@code check.OperationFactBinder}) rather than on the first ask for each fact. Bound the second
 * way, a fact nothing asked for was a fact nothing checked, and the completeness of the checking
 * depended on which consumers there happened to be.
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
        List<Declared> out = new ArrayList<>(List.of(
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

            // The operations whose result is a number taken of the one value they are given.
            about("List", "length", new OperationFact.CountsWhatItIsGiven()),
            about("String", "length", new OperationFact.CountsWhatItIsGiven()),
            about("Set", "size", new OperationFact.CountsWhatItIsGiven()),
            about("Map", "size", new OperationFact.CountsWhatItIsGiven()),
            about("String", "length",
                    new OperationFact.EveryCountItGivesIsACountSomeValueHas()),

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
            about("Map", "updateIfPresent", new OperationFact.BuildsItsResultFrom(new BuiltFrom(
                    new ElementLineage.OneOf(List.of(
                            new ElementLineage.SameAs(new ElementLineage.Source(CONTAINER, 1)),
                            new ElementLineage.ClosureResult(
                                    new ElementLineage.Source(CONTAINER, 1)))),
                    SizeAgainstItsSource.SAME))),
            // Inside what the closure answered, which is an optional here and a list in a
            // `flatMap`. One lineage for the two, told apart by what the closure's own signature
            // says it answers with.
            about("List", "filterMap", new OperationFact.BuildsItsResultFrom(new BuiltFrom(
                    new ElementLineage.InsideClosureResult(
                            new ElementLineage.Source(CONTAINER, 1)), SizeAgainstItsSource.AT_MOST))),
            about("Set", "map", maps(CONTAINER, SizeAgainstItsSource.AT_MOST)),

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
            about("Int", "divide",
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
                    stands(at(2), Rel.LE, at(1))))));

        // What a construction keeps of what it read, where the answer is nothing. Each group is
        // a reason about what a shape can say, not about the operation being uninteresting.
            //
        // They answer something other than what they read. A map's keys and its entry pairs are
        // not its values, `fromList` takes the values out of pairs, `groupBy` answers lists of
        // the elements rather than the elements, `concat` reads the lists inside its argument,
        // `zipShortest` pairs two lists, and `flatMap` makes any number of elements from each.
            //
        // They put in what the container they read did not hold. Nothing that held of every
        // element still does. How many there are is said instead by the bound on the result.
            //
        // They answer the same elements in a container of another kind. That is true and
        // unsayable: every statement names the kind it is about, so nothing said of a list is a
        // statement about a set, and a rule between them would carry nothing.
        out.addAll(saysNothing(OperationSubject.BUILT, op("Map", "keys"), op("Map", "toList"), op("Map", "fromList"),
                op("List", "groupBy"), op("List", "concat"), op("List", "zipShortest"), op("List", "flatMap"),
                op("Map", "insert"), op("Set", "insert"), op("Map", "union"), op("Set", "union"), op("List", "append"),
                op("Map", "updateOrInsert"), op("Map", "values"), op("Set", "toList"), op("Set", "fromList"),
                op("List", "indexBy")));

        // A predicate over a string states something of the characters it holds in the order it
        // holds them, and what would carry such a statement is a construction of a container
        // from a container, which a string is not one of. An emptiness check is carried by what
        // its size does and not as a property of elements.
        out.addAll(saysNothing(OperationSubject.PREDICATE_CARRY, op("String", "contains"), op("String", "startsWith"),
                op("String", "endsWith"), op("String", "matches"), op("List", "isEmpty"), op("Set", "isEmpty"),
                op("Map", "isEmpty"), op("String", "isEmpty")));

        // `List.any` states its predicate of some element and not of every one.
        out.addAll(saysNothing(OperationSubject.QUANTIFICATION, op("List", "any")));

        // Their result is not bounded by their arguments at all. The arithmetic and its
        // function forms answer a number that may be anywhere; a comparison answers a sign,
        // which is what the order it decides says; a choice answers one of two values, and what
        // that bounds follows from the case it is in.
        out.addAll(saysNothing(OperationSubject.BOUNDS, op("Int", "add"), op("Int", "subtract"), op("Int", "multiply"),
                op("Decimal", "add"), op("Decimal", "subtract"), op("Decimal", "multiply"), op("Int", "compare"),
                op("Decimal", "compare"), op("Int", "min"), op("Int", "max"), op("Int", "clamp"), op("Decimal", "min"),
                op("Decimal", "max"), op("Decimal", "clamp"), op("Decimal", "fromInt"), op("Decimal", "round")));

        // Months and years hold different numbers of days, so neither states a count of the one
        // measure a pair of dates has.
        out.addAll(saysNothing(OperationSubject.MEASURE, op("Date", "addMonths"), op("Date", "addYears")));

        // They compute a new number rather than answering one they were given: what `a + b`
        // answers is neither `a` nor `b`, `compare` answers a sign, `floorMod` a remainder,
        // `abs` a distance, `toInt` a whole number, `round` a value at another scale.
        // `Decimal.fromInt` answers the number it was given unconditionally, which is a
        // statement of its own rather than a case.
        out.addAll(saysNothing(OperationSubject.CHOICE, op("Int", "add"), op("Int", "subtract"), op("Int", "multiply"),
                op("Decimal", "add"), op("Decimal", "subtract"), op("Decimal", "multiply"), op("Int", "compare"),
                op("Decimal", "compare"), op("Int", "floorMod"), op("Int", "abs"), op("Decimal", "abs"), op("Decimal", "toInt"),
                op("Decimal", "round"), op("Decimal", "fromInt")));

        // They answer one of the values they were given, which is which case they are in and
        // not arithmetic of their own.
        out.addAll(saysNothing(OperationSubject.NUMERIC_RESULT, op("Int", "min"), op("Int", "max"), op("Int", "clamp"),
                op("Int", "floorMod"), op("Int", "compare"), op("Decimal", "min"), op("Decimal", "max"), op("Decimal", "clamp")));

        // Arithmetic and a choice between two values are not orders at all: what
        // `Int.subtract` answers has the sign of one and says how far apart they are as well,
        // and `min` answers one of the two rather than anything about the pair.
        // `DateTime.minutesBetween` counts whole minutes, so a zero says the two are less than
        // a minute apart rather than that they are equal, and a non-negative count does not say
        // the second is not the earlier.
        out.addAll(saysNothing(OperationSubject.ORDER, op("Int", "add"), op("Int", "subtract"), op("Int", "multiply"),
                op("Int", "min"), op("Int", "max"), op("Int", "floorMod"), op("DateTime", "minutesBetween")));

        // What they answer is no form of what they were given, for three reasons.
        //
        // A product is one only where an operand is written down: `Int.multiply(a, b)` is
        // arithmetic over `a` and `b` and is a form of neither, since what multiplies each is the
        // other. A sum and a difference are not here at all — what they answer is a form of what
        // they were given, and they say so by being the arithmetic they are — the operator a call
        // to them is read as, which `ComputesANumber` records. A silence here would deny
        // that, which is why the two cannot both be written: a name under a subject says nothing is
        // true of it there.
        //
        // A number of their own: `compare` answers a sign, `floorMod` a remainder, `abs` a distance
        // with the sign dropped, `toInt` a whole number, `round` a value at another scale. What such
        // a result is bounded by is a different statement from its being a value that was already
        // there; and `min`, `max` and `clamp` answer one of their arguments, which one depending on
        // the arguments, and that is what their cases say.
        //
        // And, among the temporal ones, a count that is not arithmetic over the counts it was
        // given. Months and years hold different numbers of days, so neither shift moves a date by
        // any number of them. `DateTime.minutesBetween` counts whole minutes over a carrier
        // counting seconds and drops the remainder toward zero, so it is not the difference of the
        // two counts — which is why it is the operation an author of the next such fact would reach
        // for, and why the refusal is written down beside the ones that are accepted. A component
        // is read out of a count by dividing or by taking a remainder: the year a day falls in, the
        // second within a minute, the day a second falls in, the second within a day.
        out.addAll(saysNothing(OperationSubject.FORM, op("Int", "multiply"),
                op("Decimal", "multiply"), op("Int", "compare"),
                op("Decimal", "compare"), op("Int", "floorMod"), op("Int", "abs"), op("Decimal", "abs"), op("Decimal", "toInt"),
                op("Decimal", "round"), op("Int", "min"), op("Int", "max"), op("Int", "clamp"), op("Decimal", "min"), op("Decimal", "max"),
                op("Decimal", "clamp"), op("Date", "addMonths"), op("Date", "addYears"),
                op("DateTime", "minutesBetween"), op("Date", "year"), op("Date", "month"),
                op("Date", "day"), op("Time", "hour"), op("Time", "minute"), op("Time", "second"),
                op("DateTime", "toDate"), op("DateTime", "toTime")));
        return List.copyOf(out);
    }

    /** That there is nothing to say of each of {@code operations} under {@code subject}. */
    private static List<Declared> saysNothing(OperationSubject subject, ValueName... operations) {
        List<Declared> out = new ArrayList<>(operations.length);
        for (ValueName operation : operations) {
            out.add(new Declared(operation, new OperationFact.SaysNothingOf(subject)));
        }
        return out;
    }

    /** The operation {@code name} of the library module published as {@code alias}. Written as the
     *  two values it is, so that a declaration says which library it is about without a reader
     *  splitting a spelling to find out. */
    private static ValueName op(String alias, String name) {
        return new ValueName.Stdlib(alias, name);
    }

    private static OperationFact computes(Arithmetic arithmetic) {
        return new OperationFact.ComputesANumber(new NumericResult(
                new NumericResult.Answered.Directly(), arithmetic, null));
    }

    /** The condition every division comes back as {@code DivisionByZero} under. */
    private static OperationFact computesInTheCaseCarrying(Type carried, Arithmetic arithmetic) {
        return new OperationFact.ComputesANumber(new NumericResult(
                new NumericResult.Answered.InTheCaseCarrying(carried), arithmetic,
                new NumericResult.TheOtherCaseWhen(at(1), BinOp.EQ, 0)));
    }

    private static OperationFact answers(ArgumentRef argument,
                                         OperationFact.ArgumentsStand... given) {
        return new OperationFact.IsDefinedByCases(
                new OperationFact.Case(argument, List.of(given)));
    }

    private static OperationFact.ArgumentsStand stands(ArgumentRef left, Rel rel,
                                                       ArgumentRef right) {
        return new OperationFact.ArgumentsStand(left, rel, right);
    }

    private static OperationFact noSmallerThan(ArgumentRef container) {
        return new OperationFact.ResultIsNoSmallerThan(container);
    }

    private static OperationFact reads(ArgumentRef container, ElementShape... through) {
        return new OperationFact.ReadsItsContainer(container, java.util.Set.of(through));
    }

    private static OperationFact meansSizeOf(String module, String size) {
        return new OperationFact.MeansTheSameAsASizeOfNought(new ValueName.Stdlib(module, size));
    }

    /** The answer holds the very elements {@code source} held. */
    private static OperationFact keeps(ArgumentRef source, SizeAgainstItsSource size) {
        return new OperationFact.BuildsItsResultFrom(new BuiltFrom(
                new ElementLineage.SameAs(new ElementLineage.Source(source, 1)), size));
    }

    /** The answer holds what a closure made of each of {@code source}'s elements. */
    private static OperationFact maps(ArgumentRef source, SizeAgainstItsSource size) {
        return new OperationFact.BuildsItsResultFrom(new BuiltFrom(
                new ElementLineage.ClosureResult(new ElementLineage.Source(source, 1)), size));
    }

    /** {@code times} of what one argument is counted as. */
    private static souther.compiler.numeric.NumericDomain.LinearForm<ArgumentRef> form(
            ArgumentRef argument, long times) {
        return souther.compiler.numeric.NumericDomain.LinearForm.<ArgumentRef>atom(argument)
                .times(java.math.BigDecimal.valueOf(times));
    }

    private static OperationFact answers(
            souther.compiler.numeric.NumericDomain.LinearForm<ArgumentRef> form) {
        return new OperationFact.AnswersAFormOfItsArguments(form);
    }

    private static OperationFact bounded(Rel rel, long n) {
        return bounded(rel, null, n, new ResultBound.Provided.Always());
    }

    private static OperationFact bounded(Rel rel, long n, ResultBound.Provided provided) {
        return bounded(rel, null, n, provided);
    }

    private static OperationFact bounded(Rel rel, ArgumentRef against, long offset,
                                         ResultBound.Provided provided) {
        return new OperationFact.BoundsItsResult(
                new ResultBound(against, java.math.BigDecimal.valueOf(offset), rel, provided));
    }

    private static ResultBound.Provided always() {
        return new ResultBound.Provided.Always();
    }

    private static ResultBound.Provided aboveZero(ArgumentRef argument) {
        return new ResultBound.Provided.ConstantAboveZero(argument);
    }

    private static OperationFact shifts(String module, String measure, ArgumentRef of,
                                        ArgumentRef amount, long per) {
        return new OperationFact.ShiftsBy(new ValueName.Stdlib(module, measure), of, amount,
                java.math.BigDecimal.valueOf(per));
    }

    /** Every fact declared, for whatever holds them to the library's declarations. */
    public static List<Declared> declarations() {
        return DECLARED;
    }

    /** What {@code operation} answers, counted, in what its arguments are counted as — or null
     *  where it states no such form. */
    public static souther.compiler.numeric.NumericDomain.LinearForm<ArgumentRef>
            answersAFormOfItsArguments(ValueName operation) {
        return Index.ANSWERS_A_FORM.get(operation);
    }

    /** The operations declared to answer a form of their arguments. */
    public static java.util.Set<ValueName> answersAFormOfItsArguments() {
        return Index.ANSWERS_A_FORM.keySet();
    }

    /** Which of {@code operation}'s two arguments a positive answer names as the greater, or null
     *  where the sign of what it answers is not their order. */
    public static PositiveOrder statesTheOrderOfItsArguments(ValueName operation) {
        return Index.ORDERS.get(operation);
    }

    /** The operations whose answer states the order of their arguments. */
    public static java.util.Set<ValueName> statesTheOrderOfItsArguments() {
        return Index.ORDERS.keySet();
    }

    /** How {@code operation} moves the value it is given, or null where it moves none. */
    public static OperationFact.ShiftsBy shiftsBy(ValueName operation) {
        return Index.SHIFTS.get(operation);
    }

    /** The operations that move a value by an amount. */
    public static java.util.Set<ValueName> shiftsBy() {
        return Index.SHIFTS.keySet();
    }

    /** What holds of the number {@code operation} answers, wherever it is called. */
    public static List<ResultBound> boundsOnTheResult(ValueName operation) {
        return Index.BOUNDS.getOrDefault(operation, List.of());
    }

    /** The operations something holds of the result of. */
    public static java.util.Set<ValueName> boundsOnTheResult() {
        return Index.BOUNDS.keySet();
    }

    /** What {@code operation} builds its result from, or null where it builds none. */
    public static BuiltFrom buildsItsResultFrom(ValueName operation) {
        return Index.BUILDINGS.get(operation);
    }

    /** The operations that build a container out of another. */
    public static java.util.Set<ValueName> buildsItsResultFrom() {
        return Index.BUILDINGS.keySet();
    }

    /** The containers {@code operation}'s result is never smaller than, in the order they are
     *  declared. */
    public static List<ArgumentRef> resultIsNoSmallerThan(ValueName operation) {
        return Index.NO_SMALLER_THAN.getOrDefault(operation, List.of());
    }

    /** Where {@code operation} reads the container its predicate is about, or null where it is no
     *  such predicate. */
    public static OperationFact.ReadsItsContainer readsItsContainer(ValueName operation) {
        return Index.READS.get(operation);
    }

    /** The operations that are predicates over what a container holds. */
    public static java.util.Set<ValueName> readsItsContainer() {
        return Index.READS.keySet();
    }

    /** Where {@code operation}'s predicate is stated over a projection, or null where it is stated
     *  over the element itself. */
    public static ArgumentRef isStatedOverAProjection(ValueName operation) {
        return Index.PROJECTIONS.get(operation);
    }

    /** The operations whose predicate is stated over a projection. */
    public static java.util.Set<ValueName> isStatedOverAProjection() {
        return Index.PROJECTIONS.keySet();
    }

    /** Whether {@code operation} states its predicate of every element. */
    public static boolean statesItsPredicateOfEveryElement(ValueName operation) {
        return Index.QUANTIFIERS.contains(operation);
    }

    /** The operations that do. */
    public static java.util.Set<ValueName> statesItsPredicateOfEveryElement() {
        return Index.QUANTIFIERS;
    }

    /** The size {@code operation}'s emptiness check means, or null where it is no such check. */
    public static ValueName meansTheSameAsASizeOfNought(ValueName operation) {
        return Index.EMPTINESS.get(operation);
    }

    /** The operations that ask whether a container is empty. */
    public static java.util.Set<ValueName> meansTheSameAsASizeOfNought() {
        return Index.EMPTINESS.keySet();
    }

    /** What {@code operation} computes and where it answers it, or null where it computes no
     *  arithmetic of its own. */
    public static NumericResult computesANumber(ValueName operation) {
        return operation == null ? null : Index.ARITHMETIC.get(operation);
    }

    /** The operations that compute arithmetic of their own. */
    public static java.util.Set<ValueName> computesANumber() {
        return Index.ARITHMETIC.keySet();
    }

    /** The cases {@code operation}'s definition is written in, in the order they are declared, or
     *  an empty list where it answers none of the values it was given. */
    public static List<OperationFact.Case> isDefinedByCases(ValueName operation) {
        return Index.CASES.getOrDefault(operation, List.of());
    }

    /** The operations that answer one of the values they were given. */
    public static java.util.Set<ValueName> isDefinedByCases() {
        return Index.CASES.keySet();
    }

    /** The operations declared to say nothing under {@code subject}. */
    public static java.util.Set<ValueName> saysNothingOf(OperationSubject subject) {
        return Index.SILENCES.getOrDefault(subject, java.util.Set.of());
    }

    /** The operations that answer a number taken of the one value they are given. */
    public static java.util.Set<ValueName> countsWhatItIsGiven() {
        return Index.COUNTS;
    }

    /** Whether every count {@code operation} could give is a count some value of the type has. */
    public static boolean everyCountItGivesIsACountSomeValueHas(ValueName operation) {
        return Index.EVERY_COUNT_HAS_A_VALUE.contains(operation);
    }

    /** The indexes, read off the declarations on the first ask. */
    private static final class Index {

        private static final Map<ValueName,
                souther.compiler.numeric.NumericDomain.LinearForm<ArgumentRef>> ANSWERS_A_FORM =
                index(OperationFact.AnswersAFormOfItsArguments.class,
                        OperationFact.AnswersAFormOfItsArguments::form);

        private static final Map<ValueName, PositiveOrder> ORDERS =
                index(OperationFact.StatesTheOrderOfItsArguments.class,
                        OperationFact.StatesTheOrderOfItsArguments::order);

        private static final Map<ValueName, OperationFact.ShiftsBy> SHIFTS =
                index(OperationFact.ShiftsBy.class, java.util.function.Function.identity());

        private static final Map<ValueName, BuiltFrom> BUILDINGS =
                index(OperationFact.BuildsItsResultFrom.class,
                        OperationFact.BuildsItsResultFrom::built);

        private static final Map<ValueName, OperationFact.ReadsItsContainer> READS =
                index(OperationFact.ReadsItsContainer.class,
                        java.util.function.Function.identity());

        private static final Map<ValueName, ArgumentRef> PROJECTIONS =
                index(OperationFact.IsStatedOverAProjection.class,
                        OperationFact.IsStatedOverAProjection::projection);

        private static final Map<ValueName, ValueName> EMPTINESS =
                index(OperationFact.MeansTheSameAsASizeOfNought.class,
                        OperationFact.MeansTheSameAsASizeOfNought::size);

        private static final java.util.Set<ValueName> QUANTIFIERS =
                stating(OperationFact.StatesItsPredicateOfEveryElement.class);

        private static final java.util.Set<ValueName> COUNTS =
                stating(OperationFact.CountsWhatItIsGiven.class);

        private static final java.util.Set<ValueName> EVERY_COUNT_HAS_A_VALUE =
                stating(OperationFact.EveryCountItGivesIsACountSomeValueHas.class);

        /** The silences, by what they are about. */
        private static final Map<OperationSubject, java.util.Set<ValueName>> SILENCES = silences();

        private static Map<OperationSubject, java.util.Set<ValueName>> silences() {
            Map<OperationSubject, java.util.Set<ValueName>> out = new LinkedHashMap<>();
            for (Declared each : DECLARED) {
                if (each.fact() instanceof OperationFact.SaysNothingOf said) {
                    out.computeIfAbsent(said.subject(), subject -> new java.util.LinkedHashSet<>())
                            .add(each.operation());
                }
            }
            out.replaceAll((subject, held) -> java.util.Set.copyOf(held));
            return Map.copyOf(out);
        }

        private static final Map<ValueName, NumericResult> ARITHMETIC =
                index(OperationFact.ComputesANumber.class, OperationFact.ComputesANumber::result);

        /** In the order they are declared, which is the order the library writes them: what holds
         *  in every case holds of the result, and that is a claim about the run of them. */
        private static final Map<ValueName, List<OperationFact.Case>> CASES = cases();

        private static Map<ValueName, List<OperationFact.Case>> cases() {
            Map<ValueName, List<OperationFact.Case>> out = new LinkedHashMap<>();
            for (Declared each : DECLARED) {
                if (each.fact() instanceof OperationFact.IsDefinedByCases defined) {
                    out.computeIfAbsent(each.operation(), operation -> new ArrayList<>())
                            .add(defined.one());
                }
            }
            out.replaceAll((operation, held) -> List.copyOf(held));
            return Map.copyOf(out);
        }

        /** Gathered rather than indexed one to one: an operation is no smaller than as many
         *  containers as it names, and each is a fact of its own. */
        private static final Map<ValueName, List<ArgumentRef>> NO_SMALLER_THAN = noSmallerThan();

        private static Map<ValueName, List<ArgumentRef>> noSmallerThan() {
            Map<ValueName, List<ArgumentRef>> out = new LinkedHashMap<>();
            for (Declared each : DECLARED) {
                if (each.fact() instanceof OperationFact.ResultIsNoSmallerThan bounded) {
                    out.computeIfAbsent(each.operation(), operation -> new ArrayList<>())
                            .add(bounded.container());
                }
            }
            out.replaceAll((operation, held) -> List.copyOf(held));
            return Map.copyOf(out);
        }

        /** Gathered rather than indexed one to one: an operation states as many bounds as it
         *  states, and each is a fact of its own. */
        private static final Map<ValueName, List<ResultBound>> BOUNDS = bounds();

        private static Map<ValueName, List<ResultBound>> bounds() {
            Map<ValueName, List<ResultBound>> out = new LinkedHashMap<>();
            for (Declared each : DECLARED) {
                if (each.fact() instanceof OperationFact.BoundsItsResult bounded) {
                    out.computeIfAbsent(each.operation(), operation -> new ArrayList<>())
                            .add(bounded.bound());
                }
            }
            out.replaceAll((operation, held) -> List.copyOf(held));
            return Map.copyOf(out);
        }

        /** The operations that carry a fact of {@code kind}, for a fact that says nothing beside
         *  being declared at all. */
        private static java.util.Set<ValueName> stating(Class<? extends OperationFact> kind) {
            java.util.Set<ValueName> out = new java.util.LinkedHashSet<>();
            for (Declared each : DECLARED) {
                if (kind.isInstance(each.fact())) {
                    out.add(each.operation());
                }
            }
            return java.util.Set.copyOf(out);
        }

        private static <F extends OperationFact, V> Map<ValueName, V> index(
                Class<F> kind, java.util.function.Function<F, V> read) {
            Map<ValueName, V> out = new LinkedHashMap<>();
            for (Declared each : DECLARED) {
                if (kind.isInstance(each.fact())) {
                    V value = read.apply(kind.cast(each.fact()));
                    if (out.put(each.operation(), value) != null) {
                        throw new IllegalStateException(each.operation()
                                + " is declared to " + kind.getSimpleName() + " twice");
                    }
                }
            }
            return Map.copyOf(out);
        }
    }

    private OperationFacts() {}
}
