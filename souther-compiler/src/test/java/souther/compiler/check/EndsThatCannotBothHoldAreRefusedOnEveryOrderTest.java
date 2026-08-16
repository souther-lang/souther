package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.Located;
import souther.compiler.query.Compilation;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * An invariant whose ends cannot both hold, refused wherever the position has an order.
 *
 * <p>It was refused over an {@code Int} and a {@code Decimal} and nowhere else. Those two are the
 * positions the interval algebra carries — it holds one number per position and only for the
 * numbers a model adds — so the count deciding whether a type has any value heard the rule there and
 * heard nothing anywhere else. A {@code Date} bounded above a date it is bounded below of compiled,
 * emitted classes, and aborted at run time on every construction.
 *
 * <p>The ends were being read the whole time. A one-sided bound on a {@code DateTime} draws a line
 * the report counts and asks for a row at, so the reading that turns a clause into an end reached
 * these positions perfectly; what it produced went to the report and to no domain, and whether a
 * value exists is asked of the domains.
 *
 * <p><b>Every order in one test.</b> Each of the eight is written here in the shape that admits
 * nothing and in the shape beside it that admits something, because what has to hold is that they
 * answer alike — a table with a row missing is an order nothing holds to the others, which is how
 * {@code Int} and {@code Date} came to differ in the first place.
 */
class EndsThatCannotBothHoldAreRefusedOnEveryOrderTest {

    private static List<String> codesFor(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        return compilation.diagnostics().values().stream()
                .flatMap(List::stream)
                .map(Located::diagnostic)
                .map(each -> each.code())
                .toList();
    }

    private static void refuses(String what, String source) {
        assertEquals(List.of("E1013"), codesFor(source), what + " admits no value");
    }

    private static void admits(String what, String source) {
        assertEquals(List.of(), codesFor(source), what + " admits a value");
    }

    private static String newtype(String carried, String rule) {
        return "module demo\n\ndata X = " + carried + "\n    invariant " + rule + "\n";
    }

    /**
     * The refusal says which position was left nothing, and not only that something contradicts.
     *
     * <p>Both readings of an {@code Int}'s ends can show this, and the ordering is the one that can
     * name what it found. So the sentence is the same one wherever the position sits and whatever
     * carries it, which is what the two issues closed here are about.
     *
     * <p>And it says what was shown rather than one of the ways of showing it. Three shapes reach
     * this proof — two ends that cross, one end the order does not reach, and two equalities naming
     * different values — and only the first of them writes a pair of bounds. A sentence about a pair
     * of bounds sends the author of the other two looking for a rule the model does not contain.
     */
    @Test
    void theRefusalNamesThePositionTheRulesLeftNothing() {
        assertEquals(List.of("NothingIsLeftForThatPositionToHold"),
                saidBy(newtype("Int", "value > 5 && value < 3")));
        assertEquals(List.of("NothingIsLeftForThatPositionToHold"),
                saidBy(newtype("Date",
                        "value > Date(\"2020-01-01\") && value < Date(\"2010-01-01\")")),
                "and the same sentence over an order the numbers do not carry");
        assertEquals(List.of("NothingIsLeftForThatPositionToHold"),
                saidBy(newtype("Time", "value > Time(\"23:59:59\")")),
                "and where one rule names an end the order does not reach");
        assertEquals(List.of("NothingIsLeftForThatPositionToHold"),
                saidBy(newtype("String", "value == \"A\" && value == \"B\"")),
                "and where two equalities name different values");
    }

    /**
     * A choice between alternatives none of which admits anything.
     *
     * <p>An alternative that admits nothing is one nobody can take, so a choice among such
     * alternatives is a rule nothing satisfies. Whether a branch admits anything is a question about
     * the whole of what is known at its positions — the rules it states and where their orders stop
     * — and a reading that added the orders only after the alternatives were joined could not ask it
     * of a branch. Then the answer turned on whether the branches happened to be empty at the same
     * position: {@code a < "" || a < ""} was refused and {@code a < "" || b < ""} was not.
     */
    @Test
    void aChoiceAmongAlternativesNoneOfWhichAdmitsAnythingIsRefused() {
        refuses("a choice between two positions neither of which can hold anything", """
                module demo

                data X = { a: String, b: String }
                    invariant no = a < "" || b < ""
                """);
        refuses("a choice between two rules about one position, neither holding anything", """
                module demo

                data X = { a: String }
                    invariant no = a < "" || a > "b" && a < "a"
                """);
    }

    /**
     * An alternative is impossible whichever reading of it shows so.
     *
     * <p>The connectives are over the clause and not over one language for reading it. Applied
     * inside each language separately, an alternative is dropped only where the language that could
     * show it impossible is also the one being joined — so a choice between a branch no order admits
     * and a branch no set of values admits was a choice both readings called open, each because the
     * other was holding the answer.
     */
    @Test
    void anAlternativeIsImpossibleWhicheverReadingShowsIt() {
        refuses("a choice between a branch no order admits and one no values admit", """
                module demo

                data X = { s: String, b: Bool }
                    invariant no = s < "" || (b == true && b == false)
                """);
        refuses("a choice between two positions, each named two values", """
                module demo

                data X = { a: Bool, b: Bool }
                    invariant no = (a == true && a == false) || (b == true && b == false)
                """);
    }

    /**
     * And the sentence is the same one whichever way round the alternatives are written.
     *
     * <p>Which sentence a refusal is follows from which proof it carries, and the proof is chosen
     * where proofs are chosen. It must not have been settled already by whichever alternative the
     * reading gave up on first.
     */
    @Test
    void aChoiceIsToldTheSameSentenceEitherWayRound() {
        assertEquals(List.of("NothingIsLeftForThatPositionToHold"), saidBy("""
                module demo

                data X = { b: Int, a: String }
                    invariant no = (a < "" && b == 0) || (a < "" && b == 1)
                """), "a position every alternative leaves nothing at is named");
        assertEquals(List.of("NothingIsLeftForThatPositionToHold"), saidBy("""
                module demo

                data X = { b: Int, a: String }
                    invariant no = (a < "" && b == 1) || (a < "" && b == 0)
                """), "and the operands the other way round");

        assertEquals(List.of("ItsRulesCannotAllHold"), saidBy("""
                module demo

                data X = { s: String, b: Bool }
                    invariant no = s < "" || (b == true && b == false)
                """), "and where no position is at fault, the general sentence");
        assertEquals(List.of("ItsRulesCannotAllHold"), saidBy("""
                module demo

                data X = { s: String, b: Bool }
                    invariant no = (b == true && b == false) || s < ""
                """), "and the operands the other way round");
    }

    /**
     * And an alternative that does admit something leaves the choice open.
     *
     * <p>The negative control for the one above. Dropping an impossible alternative must leave the
     * other one standing rather than the whole rule refused, and a position only one alternative
     * speaks about is one the two of them together leave open.
     */
    @Test
    void aChoiceWithOneAlternativeThatAdmitsSomethingIsNotRefused() {
        admits("a choice where the second alternative can be taken", """
                module demo

                data X = { a: String, b: String }
                    invariant no = a < "" || b == "x"
                """);
        admits("a choice where both alternatives can be taken", """
                module demo

                data X = { a: String, b: String }
                    invariant no = a > "" || b > ""
                """);
    }

    /** Which sentence a refusal is, named by the message rather than by its wording. */
    private static List<String> saidBy(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        return compilation.diagnostics().values().stream()
                .flatMap(List::stream)
                .map(Located::diagnostic)
                .filter(each -> "E1013".equals(each.code()))
                .map(each -> each.said().getClass().getSimpleName())
                .toList();
    }

    private static final String COLOURS = """
            module demo

            data Red
            data Green
            data Blue
            data Colour = Red | Green | Blue
            """;

    // ---- whole numbers and decimals, which were refused before any of this ----

    @Test
    void aWholeNumberBoundedAboveAValueItIsBoundedBelowOfIsRefused() {
        refuses("an `Int` above 5 and below 3", newtype("Int", "value > 5 && value < 3"));
        admits("an `Int` above 3 and below 5", newtype("Int", "value > 3 && value < 5"));
    }

    @Test
    void twoWholeNumbersWithNothingBetweenThemAreRefused() {
        refuses("an `Int` above 5 and below 6", newtype("Int", "value > 5 && value < 6"));
        admits("an `Int` above 5 and below 7", newtype("Int", "value > 5 && value < 7"));
    }

    @Test
    void aDecimalBoundedAboveAValueItIsBoundedBelowOfIsRefused() {
        refuses("a `Decimal` above 5 and below 3",
                newtype("Decimal", "value > 5.0m && value < 3.0m"));
        admits("a `Decimal` above 3 and below 5",
                newtype("Decimal", "value > 3.0m && value < 5.0m"));
    }

    // ---- the four temporals, which is what #773 is ----

    @Test
    void aDateBoundedAboveADateItIsBoundedBelowOfIsRefused() {
        refuses("a `Date` after 2020 and before 2010", newtype("Date",
                "value > Date(\"2020-01-01\") && value < Date(\"2010-01-01\")"));
        admits("a `Date` after 2010 and before 2020", newtype("Date",
                "value > Date(\"2010-01-01\") && value < Date(\"2020-01-01\")"));
    }

    @Test
    void aDateTimeBoundedAboveOneItIsBoundedBelowOfIsRefused() {
        refuses("a `DateTime` after 2020 and before 2010", newtype("DateTime",
                "value > DateTime(\"2020-01-01T00:00\") && value < DateTime(\"2010-01-01T00:00\")"));
        admits("a `DateTime` after 2010 and before 2020", newtype("DateTime",
                "value > DateTime(\"2010-01-01T00:00\") && value < DateTime(\"2020-01-01T00:00\")"));
    }

    @Test
    void aTimeBoundedAboveOneItIsBoundedBelowOfIsRefused() {
        refuses("a `Time` after 10:00 and before 09:00",
                newtype("Time", "value > Time(\"10:00\") && value < Time(\"09:00\")"));
        admits("a `Time` after 09:00 and before 10:00",
                newtype("Time", "value > Time(\"09:00\") && value < Time(\"10:00\")"));
    }

    @Test
    void anInstantBoundedAboveOneItIsBoundedBelowOfIsRefused() {
        refuses("an `Instant` after 2020 and before 2010", newtype("Instant",
                "value > Instant(\"2020-01-01T00:00:00Z\") "
                        + "&& value < Instant(\"2010-01-01T00:00:00Z\")"));
        admits("an `Instant` after 2010 and before 2020", newtype("Instant",
                "value > Instant(\"2010-01-01T00:00:00Z\") "
                        + "&& value < Instant(\"2020-01-01T00:00:00Z\")"));
    }

    /**
     * A rule stating an end a bounded order does not reach, on the two sides it has.
     *
     * <p>A day runs from midnight to the last second before the next one, and neither end is a
     * number the reading may pass. Read against a range open below, {@code value < Time("00:00")}
     * leaves room underneath a value that has none; read against one open above, a strict bound at
     * the last second leaves room above the last second there is.
     */
    @Test
    void aTimeOutsideTheDayIsRefused() {
        refuses("a `Time` below 00:00", newtype("Time", "value < Time(\"00:00\")"));
        refuses("a `Time` above 23:59:59", newtype("Time", "value > Time(\"23:59:59\")"));
        admits("a `Time` at or above 00:00", newtype("Time", "value >= Time(\"00:00\")"));
        admits("a `Time` at or below 23:59:59", newtype("Time", "value <= Time(\"23:59:59\")"));
    }

    /** An equality states both ends at once, which is a range with one value in it. */
    @Test
    void aDateSaidToBeTwoDatesIsRefused() {
        refuses("a `Date` that is both 2020-01-01 and 2010-01-01", newtype("Date",
                "value == Date(\"2020-01-01\") && value == Date(\"2010-01-01\")"));
        admits("a `Date` that is 2020-01-01 twice over", newtype("Date",
                "value == Date(\"2020-01-01\") && value == Date(\"2020-01-01\")"));
    }

    // ---- strings, which neither issue names and which fall the same way ----

    @Test
    void aStringBoundedAboveOneItIsBoundedBelowOfIsRefused() {
        refuses("a `String` above \"b\" and below \"a\"",
                newtype("String", "value > \"b\" && value < \"a\""));
        admits("a `String` above \"a\" and below \"b\"",
                newtype("String", "value > \"a\" && value < \"b\""));
    }

    /**
     * A string below the empty one, which is a bound the order does not reach.
     *
     * <p>The end nothing is under. Read as a range open below — which is what a reading starting
     * every position unbounded does — this admits everything under a string that has nothing under
     * it.
     */
    @Test
    void aStringBelowTheEmptyStringIsRefused() {
        refuses("a `String` below \"\"", newtype("String", "value < \"\""));
        admits("a `String` at or above \"\"", newtype("String", "value >= \"\""));
    }

    /**
     * A string above one, which admits every string beginning with it.
     *
     * <p>The negative control. There is no next string this language names, so a reading that
     * decided emptiness by asking for a value to write would answer "none" here — and answer it
     * about a position holding endlessly many.
     */
    @Test
    void aStringAboveOneIsNotRefusedForWantOfANameToWriteAtIt() {
        admits("a `String` above \"a\"", newtype("String", "value > \"a\""));
    }

    // ---- enumerations, which is what #780 is ----

    @Test
    void anEnumerationAboveItsLastCaseIsRefused() {
        refuses("a `Colour` above `Blue`", COLOURS + """

                data P = { c: Colour }
                    invariant c > Blue
                """);
        admits("a `Colour` above `Red`", COLOURS + """

                data P = { c: Colour }
                    invariant c > Red
                """);
    }

    @Test
    void anEnumerationBoundedAboveACaseItIsBoundedBelowOfIsRefused() {
        refuses("a `Colour` at or above `Blue` and at or below `Red`", COLOURS + """

                data P = { c: Colour }
                    invariant c >= Blue && c <= Red
                """);
        admits("a `Colour` at or above `Red` and at or below `Blue`", COLOURS + """

                data P = { c: Colour }
                    invariant c >= Red && c <= Blue
                """);
    }

    /** The same rule under a name wrapped round the enumeration, which is the same position. */
    @Test
    void aNameWrappedRoundAnEnumerationIsBoundedTheSameWay() {
        refuses("a `Painted` above `Blue`", COLOURS + """

                data Painted = Colour
                    invariant value > Blue
                """);
        admits("a `Painted` above `Red`", COLOURS + """

                data Painted = Colour
                    invariant value > Red
                """);
    }
}
