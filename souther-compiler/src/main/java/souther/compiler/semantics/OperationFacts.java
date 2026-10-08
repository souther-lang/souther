package souther.compiler.semantics;

import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.types.BinOp;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

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

    /** The closure the signature says is handed the container's elements. */
    private static final ArgumentRef CLOSURE = new ArgumentRef.TheClosure();

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
            about("Date", "daysBetween", answers(forms(at(0), -1, at(1), 1))),
            about("Date", "addDays", answers(forms(at(0), 1, at(1), 1))),
            // The same over the second the date-times count, which is the epoch second a local
            // value stands at: a day is eighty-six thousand four hundred of them, exactly, because
            // the value carries no zone for anything to shift it by.
            about("DateTime", "addMinutes", answers(forms(at(0), 60, at(1), 1))),
            about("DateTime", "addHours", answers(forms(at(0), 3600, at(1), 1))),
            about("DateTime", "addDays", answers(forms(at(0), 86400, at(1), 1))),
            // And the one that puts two counts together: a date counts days from the epoch and a
            // time counts seconds into its day, so the date-time they make counts the first at a
            // day's worth of seconds and the second as it stands.
            about("DateTime", "fromDateAndTime",
                    answers(forms(at(0), 86400, at(1), 1))),

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

            // Which keys a map an operation answers is keyed by, where they are keys of a map it
            // was given. A rewrite of the values keeps every key, and taking entries out keeps the
            // keys of the ones left; putting one in does not, since the key put in was no key of
            // the map.
            about("Map", "filterEntries", keepsTheKeysOf(CONTAINER)),
            about("Map", "mapValues", keepsTheKeysOf(CONTAINER)),
            about("Map", "updateIfPresent", keepsTheKeysOf(CONTAINER)),
            about("Map", "remove", keepsTheKeysOf(at(1))),
            about("Map", "intersection", keepsTheKeysOf(at(0))),
            about("Map", "difference", keepsTheKeysOf(at(0))),

            // A list of what a map holds, and which part of it.
            about("Map", "keys", lists(at(0), MapPart.KEYS)),
            about("Map", "values", lists(at(0), MapPart.VALUES)),
            about("Map", "toList", lists(at(0), MapPart.ENTRIES)),

            // What each observation of an answer comes to over the arguments. Every operation
            // whose answer has a side is asked it, and either answers here, or is answered by
            // what it builds (an answer as many as its one source, a list of what a map holds),
            // or is closed below with what the domain has no words for.
            //
            // The operations that walk a container with a closure come out as the element that
            // witnesses it. A filter holds something where some element was kept, a filterMap
            // where some element's answer held a value, a flatMap where some element's answer
            // held something; `any` is true where some element's answer is, and `all` where none
            // is false. That a filter answers at most as many as it walked is the size fact above;
            // that an element kept is one the closure held of is this.
            about("List", "filter", law(AnswerAspect.EMPTINESS, some(CONTAINER, answers(true)))),
            about("Set", "filter", law(AnswerAspect.EMPTINESS, some(CONTAINER, answers(true)))),
            about("Map", "filterEntries",
                    law(AnswerAspect.EMPTINESS, some(CONTAINER, answers(true)))),
            about("List", "filterMap", law(AnswerAspect.EMPTINESS, some(CONTAINER,
                    closureAnswers(AnswerAspect.PRESENCE)))),
            about("List", "flatMap", law(AnswerAspect.EMPTINESS, some(CONTAINER,
                    closureAnswers(AnswerAspect.EMPTINESS)))),
            about("List", "any", law(AnswerAspect.TRUTH, some(CONTAINER, answers(true)))),
            about("List", "all", law(AnswerAspect.TRUTH, some(CONTAINER, answers(false)).denied())),
            about("List", "find", law(AnswerAspect.PRESENCE, some(CONTAINER, answers(true)))),
            // And how many a filter keeps: as many elements as its closure holds of.
            about("List", "filter", size(howManyMeet(CONTAINER, answers(true)))),
            about("Set", "filter", size(howManyMeet(CONTAINER, answers(true)))),
            about("Map", "filterEntries", size(howManyMeet(CONTAINER, answers(true)))),
            about("List", "filterMap", size(howManyMeet(CONTAINER,
                    closureAnswers(AnswerAspect.PRESENCE)))),
            about("List", "append", size(sizeOf(at(0)), sizeOf(at(1)))),

            // What it was handed holding anything, where its size is not its source's: a set
            // made of a list or of what a closure answered holds one of each repeated value, a
            // distinct list one of each, a grouping one key per value it was keyed by.
            about("Set", "map", law(AnswerAspect.EMPTINESS, holdsSomething(CONTAINER))),
            about("Set", "fromList", law(AnswerAspect.EMPTINESS, holdsSomething(at(0)))),
            about("Set", "toList", law(AnswerAspect.EMPTINESS, holdsSomething(at(0)))),
            about("Map", "fromList", law(AnswerAspect.EMPTINESS, holdsSomething(at(0)))),
            about("List", "distinct", law(AnswerAspect.EMPTINESS, holdsSomething(at(0)))),
            about("List", "distinctBy", law(AnswerAspect.EMPTINESS, holdsSomething(CONTAINER))),
            about("List", "groupBy", law(AnswerAspect.EMPTINESS, holdsSomething(CONTAINER))),
            about("List", "indexBy", law(AnswerAspect.EMPTINESS, holdsSomething(CONTAINER))),
            // A string's case and order change which characters it holds and never whether it
            // holds any; how many it holds is another matter, since a case mapping can widen one
            // character to several.
            about("String", "lowercase", law(AnswerAspect.EMPTINESS, holdsSomething(at(0)))),
            about("String", "uppercase", law(AnswerAspect.EMPTINESS, holdsSomething(at(0)))),
            about("String", "reverse", law(AnswerAspect.EMPTINESS, holdsSomething(at(0)))),
            about("String", "characters", law(AnswerAspect.EMPTINESS, holdsSomething(at(0)))),
            about("String", "codePoints", law(AnswerAspect.EMPTINESS, holdsSomething(at(0)))),
            about("Option", "map", law(AnswerAspect.PRESENCE,
                    new LawProposition.Observed<>(new LawSubject.Argument<>(CONTAINER),
                            new SideAnswered(AnswerAspect.PRESENCE, true)))),
            about("List", "max", law(AnswerAspect.PRESENCE, holdsSomething(at(0)))),
            about("List", "min", law(AnswerAspect.PRESENCE, holdsSomething(at(0)))),

            // Two of them, either or both.
            about("List", "append", law(AnswerAspect.EMPTINESS,
                    any(holdsSomething(at(0)), holdsSomething(at(1))))),
            about("String", "append", law(AnswerAspect.EMPTINESS,
                    any(holdsSomething(at(0)), holdsSomething(at(1))))),
            about("Set", "union", law(AnswerAspect.EMPTINESS,
                    any(holdsSomething(at(0)), holdsSomething(at(1))))),
            about("Map", "union", law(AnswerAspect.EMPTINESS,
                    any(holdsSomething(at(0)), holdsSomething(at(1))))),
            about("List", "zipShortest", law(AnswerAspect.EMPTINESS,
                    all(holdsSomething(at(0)), holdsSomething(at(1))))),
            // Some element that holds something, of a list of containers put end to end; and a
            // separator holds something between two of them.
            about("List", "concat", law(AnswerAspect.EMPTINESS, some(at(0),
                    holdsSomething(new LawSubject.ElementOf<>(at(0)))))),
            about("String", "concat", law(AnswerAspect.EMPTINESS, some(at(0),
                    holdsSomething(new LawSubject.ElementOf<>(at(0)))))),
            about("String", "join", law(AnswerAspect.EMPTINESS, any(
                    some(at(1), holdsSomething(new LawSubject.ElementOf<>(at(1)))),
                    all(atLeast(sizeOf(at(1)), 1, -2), holdsSomething(at(0)))))),

            // Asked for some and handed some. A count of nought or less takes nothing and drops
            // nothing, and one past the end takes the whole and drops all of it.
            about("List", "take", law(AnswerAspect.EMPTINESS,
                    all(atLeast(number(at(0)), 1, -1), holdsSomething(at(1))))),
            about("List", "drop", law(AnswerAspect.EMPTINESS, all(holdsSomething(at(1)),
                    atLeast(sizeOf(at(1)), 1, number(at(0)), -1, -1)))),
            about("String", "repeat", law(AnswerAspect.EMPTINESS,
                    all(atLeast(number(at(0)), 1, -1), holdsSomething(at(1))))),
            about("String", "padLeft", law(AnswerAspect.EMPTINESS, any(holdsSomething(at(2)),
                    all(atLeast(number(at(0)), 1, -1), holdsSomething(at(1)))))),
            about("String", "padRight", law(AnswerAspect.EMPTINESS, any(holdsSomething(at(2)),
                    all(atLeast(number(at(0)), 1, -1), holdsSomething(at(1)))))),
            about("List", "rangeInclusive", law(AnswerAspect.EMPTINESS,
                    atLeast(number(at(1)), 1, number(at(0)), -1, 0))),
            about("String", "slice", law(AnswerAspect.EMPTINESS,
                    atLeast(number(at(1)), 1, number(at(0)), -1, -1))),
            about("List", "get", law(AnswerAspect.PRESENCE, all(atLeast(number(at(0)), 1, 0),
                    atLeast(sizeOf(at(1)), 1, number(at(0)), -1, -1)))),

            // What answers something whatever it is handed: a value put in, a number written
            // out, and a split, which answers the whole string where it finds no separator.
            about("Set", "singleton", law(AnswerAspect.EMPTINESS, always(true))),
            about("Set", "insert", law(AnswerAspect.EMPTINESS, always(true))),
            about("Map", "singleton", law(AnswerAspect.EMPTINESS, always(true))),
            about("Map", "insert", law(AnswerAspect.EMPTINESS, always(true))),
            about("Map", "updateOrInsert", law(AnswerAspect.EMPTINESS, always(true))),
            about("String", "fromInt", law(AnswerAspect.EMPTINESS, always(true))),
            about("String", "fromDecimal", law(AnswerAspect.EMPTINESS, always(true))),
            about("String", "split", law(AnswerAspect.EMPTINESS, always(true))),
            about("String", "lines", law(AnswerAspect.EMPTINESS, always(true))),
            // And what holds nothing whatever it is handed.
            about("Set", "empty", law(AnswerAspect.EMPTINESS, always(false))),
            about("Map", "empty", law(AnswerAspect.EMPTINESS, always(false))),

            // Which values of a set are left: some other than the one taken out, some of one also
            // in the other, some of one in no element of the other.
            about("Set", "remove", law(AnswerAspect.EMPTINESS, some(at(1), new LawProposition.Same<>(
                    new LawSubject.ElementOf<>(at(1)), new LawSubject.Argument<>(at(0)), false)))),
            about("Set", "intersection", law(AnswerAspect.EMPTINESS, some(at(0),
                    some(at(1), sameElements(at(0), at(1)))))),
            about("Set", "difference", law(AnswerAspect.EMPTINESS, some(at(0),
                    some(at(1), sameElements(at(0), at(1))).denied()))),

            // And what the domain has no words for.
            about("String", "trim", unsaid(AnswerAspect.EMPTINESS,
                    Unsayable.EVERY_CHARACTER_IS_WHITESPACE)),
            about("String", "words", unsaid(AnswerAspect.EMPTINESS,
                    Unsayable.EVERY_CHARACTER_IS_WHITESPACE)),
            about("String", "replace", unsaid(AnswerAspect.EMPTINESS,
                    Unsayable.MADE_UP_OF_COPIES_OF_A_TEXT)),
            about("Map", "get", unsaid(AnswerAspect.PRESENCE, Unsayable.A_KEY_OF_A_MAP)),
            about("Map", "remove", unsaid(AnswerAspect.EMPTINESS, Unsayable.A_KEY_OF_A_MAP)),
            about("Map", "intersection", unsaid(AnswerAspect.EMPTINESS, Unsayable.A_KEY_OF_A_MAP)),
            about("Map", "difference", unsaid(AnswerAspect.EMPTINESS, Unsayable.A_KEY_OF_A_MAP)),

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
            about("List", "contains", new OperationFact.AsksWhetherItsContainerHolds(at(0))),
            about("Set", "contains", new OperationFact.AsksWhetherItsContainerHolds(at(0))),

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

    /** The answer is keyed by keys {@code map} was keyed by. */
    private static OperationFact keepsTheKeysOf(ArgumentRef map) {
        return new OperationFact.KeepsTheKeysOf(map);
    }

    /** The answer is a list of {@code part} of {@code map}. */
    private static OperationFact lists(ArgumentRef map, MapPart part) {
        return new OperationFact.ListsAPartOf(map, part);
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

    /** The answer comes out on {@code aspect}'s holding side exactly where {@code equivalentTo}
     *  holds of the arguments. */
    private static OperationFact law(AnswerAspect aspect,
                                     LawProposition<ArgumentRef> equivalentTo) {
        return new OperationFact.HasALaw(new OperationLaw.Observation<>(aspect, equivalentTo));
    }

    /** The answer holds as many as {@code parts} come to together. */
    @SafeVarargs
    private static OperationFact size(LawNumber<ArgumentRef>... parts) {
        Map<LawNumber<ArgumentRef>, ExactRatio> coefs = new LinkedHashMap<>();
        for (LawNumber<ArgumentRef> part : parts) {
            coefs.put(part, ExactRatio.ONE);
        }
        return new OperationFact.HasALaw(new OperationLaw.Size<>(
                new LinearForm<>(ExactRatio.ZERO, coefs)));
    }

    /** What an observation of the answer on {@code aspect} comes to is {@code why}, which the
     *  domain has no words for. */
    private static OperationFact unsaid(AnswerAspect aspect, Unsayable why) {
        return new OperationFact.LeavesUnsaid(OperationLaw.Observed.of(aspect), why);
    }

    private static LawProposition<ArgumentRef> always(boolean holds) {
        return new LawProposition.Always<>(holds);
    }

    private static LawProposition<ArgumentRef> all(LawProposition<ArgumentRef> one,
                                                   LawProposition<ArgumentRef> other) {
        return new LawProposition.All<>(List.of(one, other));
    }

    private static LawProposition<ArgumentRef> any(LawProposition<ArgumentRef> one,
                                                   LawProposition<ArgumentRef> other) {
        return new LawProposition.Any<>(List.of(one, other));
    }

    /** The argument at {@code argument} holding something. */
    private static LawProposition<ArgumentRef> holdsSomething(ArgumentRef argument) {
        return holdsSomething(new LawSubject.Argument<>(argument));
    }

    private static LawProposition<ArgumentRef> holdsSomething(LawSubject<ArgumentRef> subject) {
        return new LawProposition.Observed<>(subject,
                new SideAnswered(AnswerAspect.EMPTINESS, true));
    }

    /** Some element of {@code container} meeting {@code ofTheElement}. */
    private static LawProposition<ArgumentRef> some(ArgumentRef container,
                                                    LawProposition<ArgumentRef> ofTheElement) {
        return new LawProposition.SomeElement<>(container, ofTheElement, true);
    }

    /** The operation's closure, handed an element, answering a truth that comes out as
     *  {@code holds}. */
    private static LawProposition<ArgumentRef> answers(boolean holds) {
        return new LawProposition.Observed<>(new LawSubject.WhatTheClosureAnswers<>(CLOSURE),
                new SideAnswered(AnswerAspect.TRUTH, holds));
    }

    /** The operation's closure, handed an element, answering a value that comes out on the
     *  holding side of {@code aspect}. */
    private static LawProposition<ArgumentRef> closureAnswers(AnswerAspect aspect) {
        return new LawProposition.Observed<>(new LawSubject.WhatTheClosureAnswers<>(CLOSURE),
                new SideAnswered(aspect, true));
    }

    /** The element of {@code one} the statement is about being the element of {@code other} it
     *  is about. */
    private static LawProposition<ArgumentRef> sameElements(ArgumentRef one, ArgumentRef other) {
        return new LawProposition.Same<>(new LawSubject.ElementOf<>(one),
                new LawSubject.ElementOf<>(other), true);
    }

    private static LawNumber<ArgumentRef> number(ArgumentRef argument) {
        return new LawNumber.AnArgument<>(argument);
    }

    private static LawNumber<ArgumentRef> sizeOf(ArgumentRef argument) {
        return new LawNumber.SizeOf<>(new LawSubject.Argument<>(argument));
    }

    private static LawNumber<ArgumentRef> howManyMeet(ArgumentRef container,
                                                      LawProposition<ArgumentRef> ofTheElement) {
        return new LawNumber.HowManyMeet<>(container, ofTheElement);
    }

    /** {@code by · a + constant >= 0}. */
    private static LawProposition<ArgumentRef> atLeast(LawNumber<ArgumentRef> a, long by,
                                                       long constant) {
        return new LawProposition.Compared<>(new LinearForm<>(ExactRatio.of(constant),
                Map.of(a, ExactRatio.of(by))), Rel.GE);
    }

    /** {@code byA · a + byB · b + constant >= 0}. */
    private static LawProposition<ArgumentRef> atLeast(LawNumber<ArgumentRef> a, long byA,
                                                       LawNumber<ArgumentRef> b, long byB,
                                                       long constant) {
        return new LawProposition.Compared<>(new LinearForm<>(ExactRatio.of(constant),
                Map.of(a, ExactRatio.of(byA), b, ExactRatio.of(byB))), Rel.GE);
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
    private static LinearForm<ArgumentRef> form(ArgumentRef argument, long times) {
        return LinearForm.weighing(argument, ExactRatio.of(times));
    }

    /** {@code first} of one argument and {@code second} of another, which are two arguments and so
     *  two atoms of the form. */
    private static LinearForm<ArgumentRef> forms(ArgumentRef one, long first,
                                                 ArgumentRef other, long second) {
        return new LinearForm<>(ExactRatio.ZERO,
                Map.of(one, ExactRatio.of(first), other, ExactRatio.of(second)));
    }

    private static OperationFact answers(LinearForm<ArgumentRef> form) {
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
