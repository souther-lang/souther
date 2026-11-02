package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.OfferingRequest;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;
import souther.runtime.Strings;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A piece of a string split at a separator being held to a string predicate is a statement about
 * the string, and divides the position the string stands at into the strings that hold such a
 * piece and those that hold none.
 *
 * <p>Held against the runtime: the rows the model is offered are one for each side of what the
 * condition comes to for the string, as the runtime's own {@code split} and the predicate say, and
 * a row on one side is never taken for a row on the other. Every predicate over a string, every
 * quantifier over the pieces and every window of them is asked, since each is one reading and not
 * a reading for the one a model happened to write.
 */
class AConditionHoldingAPieceOfASplitToAPatternDividesTheStringTest {

    private static final String SPLIT = "String.split(\";\", list.value)";

    /** A predicate over a piece, as written about {@code t}, and as Java says it. */
    private record Held(String written, Predicate<String> holds) {}

    private static final Map<String, Held> PREDICATES = Map.of(
            "matches", new Held("String.matches(\"[A-Z]{2}[0-9]\", t)",
                    piece -> Pattern.matches("[A-Z]{2}[0-9]", piece)),
            "starts with", new Held("String.startsWith(\"JP\", t)", piece -> piece.startsWith("JP")),
            "ends with", new Held("String.endsWith(\"JP\", t)", piece -> piece.endsWith("JP")),
            "contains", new Held("String.contains(\"JP\", t)", piece -> piece.contains("JP")));

    /** The pieces a quantifier is asked over, as written and as Java keeps them. */
    private record Window(String written, Function<List<String>, Stream<String>> pieces) {}

    private static final Map<String, Window> WINDOWS = Map.of(
            "all", new Window(SPLIT, List::stream),
            "past the first", new Window("List.drop(1, " + SPLIT + ")",
                    pieces -> pieces.stream().skip(1)),
            "two past the first", new Window("List.take(2, List.drop(1, " + SPLIT + "))",
                    pieces -> pieces.stream().skip(1).limit(2)),
            "the first two, past the first", new Window("List.drop(1, List.take(2, " + SPLIT + "))",
                    pieces -> pieces.stream().limit(2).skip(1)));

    /** A quantifier over the pieces: how it is written round the closure, and what it comes to. */
    private enum Quantifier {
        SOME("List.any(t -> %s, %s)", (stream, held) -> stream.anyMatch(held)),
        EVERY("List.all(t -> %s, %s)", (stream, held) -> stream.allMatch(held)),
        SOME_THAT_FAILS("List.any(t -> Bool.not(%s), %s)",
                (stream, held) -> stream.anyMatch(held.negate())),
        NONE_THAT_FAILS("List.all(t -> Bool.not(%s), %s)",
                (stream, held) -> stream.noneMatch(held));

        private final String written;
        private final java.util.function.BiPredicate<Stream<String>, Predicate<String>> comes;

        Quantifier(String written,
                   java.util.function.BiPredicate<Stream<String>, Predicate<String>> comes) {
            this.written = written;
            this.comes = comes;
        }
    }

    /** One condition, and what it comes to for a string. */
    private record Condition(String written, Predicate<String> ofTheString) {}

    private static Condition condition(Held held, Quantifier quantifier, Window window) {
        return new Condition(quantifier.written.formatted(held.written(), window.written()),
                text -> quantifier.comes.test(window.pieces().apply(Strings.split(text, ";")),
                        held.holds()));
    }

    private static Map<String, Condition> conditions() {
        Map<String, Condition> out = new LinkedHashMap<>();
        for (Map.Entry<String, Held> held : PREDICATES.entrySet()) {
            boolean pattern = held.getKey().equals("matches");
            for (Quantifier quantifier : Quantifier.values()) {
                for (Map.Entry<String, Window> window : WINDOWS.entrySet()) {
                    // The pattern across everything asked; the predicates beside it across the
                    // quantifiers and the whole and one window, which are the same reading.
                    if (!pattern && !window.getKey().equals("all")
                            && !window.getKey().equals("past the first")) {
                        continue;
                    }
                    out.put(quantifier + " piece " + held.getKey() + ", " + window.getKey(),
                            condition(held.getValue(), quantifier, window.getValue()));
                }
            }
        }
        return out;
    }

    private static String model(String condition, String declarations) {
        return """
                module example.codes

                data Codes = String
                %s

                behavior hasCode : (list: Codes) -> Bool
                let hasCode (list) = if %s then true else false
                """.formatted(declarations, condition);
    }

    private static Compilation measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors(), "the model compiles");
        return compilation;
    }

    private static List<String> offeredFor(Compilation compilation, Pattern value) {
        String offered = GeneratedRows.of(
                Adequacy.offeredFor(compilation.db(),
                        OfferingRequest.overTheModule("example.codes")),
                Map.of(), SourceRendering.namedByIdentity(compilation.texts()),
                compilation.db()).text();
        List<String> values = new ArrayList<>();
        Matcher found = value.matcher(offered);
        while (found.find()) {
            values.add(found.group(1));
        }
        return values;
    }

    private static final Pattern A_CODE = Pattern.compile("Codes\\(\"([^\"]*)\"\\)");

    /**
     * Two rows are offered, and the condition comes out true for one and false for the other, as
     * the runtime parts the string into pieces and as the predicate holds of them: a row for the
     * strings with such a piece and one for those with none, and never two of the same side.
     */
    @Test
    void theRowsOfferedStandOnTheTwoSidesOfWhatTheConditionComesTo() {
        conditions().forEach((name, condition) -> {
            List<String> rows = offeredFor(measured(model(condition.written(), "")), A_CODE);
            assertEquals(2, rows.size(), () -> name + ": " + rows);
            assertNotEquals(condition.ofTheString().test(rows.get(0)),
                    condition.ofTheString().test(rows.get(1)),
                    () -> name + ": two rows of one side: " + rows);
        });
    }

    private static String report(String condition, String rows) {
        return report(condition, "", rows);
    }

    private static String report(String condition, String declarations, String rows) {
        Compilation compilation = measured(model(condition, declarations) + rows);
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static final String SOME_CODE = conditionOf("matches", Quantifier.SOME, "all");

    private static String conditionOf(String held, Quantifier quantifier, String window) {
        return condition(PREDICATES.get(held), quantifier, WINDOWS.get(window)).written();
    }

    /**
     * A row on each side of the condition meets both classes, and nothing is left owed. The pieces
     * are walked, so two rows of two pieces, the one that is a code first and then last, tell the
     * walk from one stopping after its first piece and from one handed the seed.
     */
    @Test
    void aRowOnEachSideMeetsBothClasses() {
        String report = report(SOME_CODE, """

                example hasCode
                    | "one" : (Codes("AB7")) -> true
                    | "none" : (Codes("")) -> false
                    | "a code second" : (Codes(";AB7")) -> true
                    | "a code first" : (Codes("AB7;")) -> true
                """);
        assertTrue(report.contains("equivalence partitions 2/2"), report);
        assertTrue(report.contains("adequacy: satisfied"), report);
    }

    /**
     * A row on one side leaves the other owed. Held for both ways round, so that neither class is
     * taken as met by the row of the other.
     */
    @Test
    void aRowOnOneSideLeavesTheOtherClassOwed() {
        for (String only : List.of("""

                example hasCode
                    | "one" : (Codes("AB7")) -> true
                """, """

                example hasCode
                    | "none" : (Codes("")) -> false
                """)) {
            String report = report(SOME_CODE, only);
            assertTrue(report.contains("equivalence partitions 1/2"), report);
            assertFalse(report.contains("adequacy: satisfied"), report);
        }
    }

    /**
     * What the type leaves of the position is met with: a string that has to be shorter than any
     * piece of the language leaves no string with such a piece, so no row is offered for a side no
     * string of the type is on.
     */
    @Test
    void aSideTheTypeLeavesNoStringOnIsNoClass() {
        List<String> rows = offeredFor(measured(model(SOME_CODE, """
                    invariant String.length(value) <= 2
                """)), A_CODE);
        assertFalse(rows.isEmpty(), "rows are offered for what the type admits");
        for (String row : rows) {
            assertTrue(row.length() <= 2 && !Pattern.matches("[A-Z]{2}[0-9]", row),
                    () -> "a row of the type that is on the side no string is on: " + rows);
        }
    }

    private static final String LISTS = """
            module example.codes

            data Codes = { codes: List<String> }

            behavior hasCode : (list: Codes) -> Bool
            let hasCode (list) = if %s then true else false
            """;

    private static final Pattern THE_CODES_OF_A_ROW = Pattern.compile("codes = \\[([^\\]]*)\\]");

    /**
     * The strings of a list are each parted: the position the statement divides is the element of
     * the list, and the rows are lists whose elements are on the two sides.
     */
    @Test
    void theElementsOfAListAreDividedWhereTheyStand() {
        Compilation compilation = Compilation.ofSource(LISTS.formatted(
                "List.any(s -> List.any(t -> String.matches(\"[A-Z]{2}[0-9]\", t),"
                        + " String.split(\";\", s)), list.codes)"), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors());
        List<String> rows = offeredFor(compilation, THE_CODES_OF_A_ROW);
        assertEquals(2, rows.size(), rows::toString);
        Predicate<String> someCodeHasAMatchingPiece = codes -> Stream.of(codes.split(","))
                .map(code -> code.strip().replace("\"", ""))
                .anyMatch(code -> Strings.split(code, ";").stream()
                        .anyMatch(piece -> Pattern.matches("[A-Z]{2}[0-9]", piece)));
        assertNotEquals(someCodeHasAMatchingPiece.test(rows.get(0)),
                someCodeHasAMatchingPiece.test(rows.get(1)), rows::toString);
    }

    /**
     * Two conditions on the pieces of one string divide it by both: the rows offered stand at
     * different places of the two, one apiece.
     */
    @Test
    void twoConditionsOnOneStringDivideItByBoth() {
        String some = conditionOf("matches", Quantifier.SOME, "all");
        String every = "List.all(t -> String.startsWith(\"A\", t), " + SPLIT + ")";
        List<String> rows = offeredFor(measured(model(some + " && " + every, "")), A_CODE);
        List<List<Boolean>> places = rows.stream().map(row -> List.of(
                condition(PREDICATES.get("matches"), Quantifier.SOME, WINDOWS.get("all"))
                        .ofTheString().test(row),
                Strings.split(row, ";").stream().allMatch(piece -> piece.startsWith("A"))))
                .toList();
        assertEquals(places.size(), places.stream().distinct().count(),
                () -> "two rows at one place of the two conditions: " + rows);
    }

    /**
     * What is asked of a piece beyond the language, or of pieces that are not the string's own, is
     * not read as the language: the model is left undetermined and no class is claimed for it.
     */
    @Test
    void whatIsNotAboutTheLanguageOfThePiecesIsLeftUnread() {
        for (String condition : List.of(
                "List.any(t -> t == \"x\", List.drop(1, " + SPLIT + "))",
                "List.any(t -> String.matches(\"[A-Z]{2}[0-9]\", t) && String.length(t) > 0, "
                        + SPLIT + ")",
                "List.any(t -> String.matches(\"[A-Z]{2}[0-9]\", t), "
                        + "String.split(\";;\", list.value))",
                "List.any(t -> String.matches(\"[A-Z]{2}[0-9]\", t), "
                        + "String.split(\";\", String.lowercase(list.value)))")) {
            String report = report(condition, "");
            assertFalse(report.contains("is divided by"), () -> condition + "\n" + report);
            assertTrue(report.contains("not read: fork"), () -> condition + "\n" + report);
        }
    }

    private static final String A_HELPER = """

            let isCode (t: String): Bool = String.matches("[A-Z]{2}[0-9]", t)
            """;

    /**
     * The rows offered for a helper stand on the two sides of what the condition comes to, as the
     * runtime parts the string and as the predicate holds of the pieces, with the window of the
     * pieces the helper is handed as the one written in place: the helper divides the string the
     * way the predicate in the closure does, and not into other classes.
     */
    @Test
    void theRowsOfferedForAHelperStandOnTheSidesTheConditionComesTo() {
        Held matches = PREDICATES.get("matches");
        for (String window : List.of("all", "past the first")) {
            Condition inPlace = condition(matches, Quantifier.SOME, WINDOWS.get(window));
            String viaAHelper = "List.any(t -> isCode(t), " + WINDOWS.get(window).written() + ")";
            List<String> placed = offeredFor(measured(model(inPlace.written(), "")), A_CODE);
            List<String> helped = offeredFor(measured(model(viaAHelper, A_HELPER)), A_CODE);
            assertEquals(2, helped.size(), () -> window + ": " + helped);
            assertEquals(placed.stream().map(inPlace.ofTheString()::test).collect(
                            java.util.stream.Collectors.toSet()),
                    helped.stream().map(inPlace.ofTheString()::test).collect(
                            java.util.stream.Collectors.toSet()),
                    () -> window + ": " + placed + " against " + helped);
            assertNotEquals(inPlace.ofTheString().test(helped.get(0)),
                    inPlace.ofTheString().test(helped.get(1)),
                    () -> window + ": two rows of one side: " + helped);
        }
    }

    /**
     * A quantifier inside another over the pieces one call parted is over another piece, and the
     * two are not read as one: a reading that was, would find every piece equal to itself and
     * divide nothing, where what is stated of two pieces of one string is not worked out.
     */
    @Test
    void anotherQuantifierOverTheSamePiecesIsNotTheSamePiece() {
        String source = """
                module example.codes

                data Codes = String

                behavior hasCode : (list: Codes) -> Bool
                let hasCode (list) = {
                    let ps = %s
                    if List.any(t -> List.any(u -> t == u, ps), ps) then true else false
                }
                """.formatted(SPLIT);
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors(), "the model compiles");
        String report = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
        assertFalse(report.contains("is divided by"), report);
        assertTrue(report.contains("not read: fork"), report);
    }

    /**
     * What a helper holds of a piece is what the closure would hold of it written in place: the
     * piece the helper is handed is the piece the closure was handed, the same call parting the
     * same string, and it divides the string as the predicate written in the closure does.
     */
    @Test
    void aPredicateHeldOfAPieceThroughAHelperDividesTheStringAsInPlace() {
        for (String condition : List.of(
                "List.any(t -> isCode(t), " + SPLIT + ")",
                "List.any(isCode, " + SPLIT + ")",
                "List.any(t -> isCode(t), List.drop(1, " + SPLIT + "))",
                "List.any(isCode, List.drop(1, " + SPLIT + "))")) {
            String report = report(condition, A_HELPER, "");
            assertTrue(report.contains("is divided by"), () -> condition + "\n" + report);
            assertFalse(report.contains("not read: fork"), () -> condition + "\n" + report);
        }
    }

    /**
     * Counts that do not fit in the numbers a window is said in are not read, and the model still
     * compiles: dropped a billion at a time, three times, the index is past every piece there can
     * be and does not come back round to a window of some.
     */
    @Test
    void aWindowTheCountsCannotSayIsNotReadAndTheModelStillCompiles() {
        for (String window : List.of(
                "List.drop(1073741823, List.drop(1073741823, List.drop(1073741823, " + SPLIT
                        + ")))",
                "List.take(9223372036854775807, " + SPLIT + ")",
                "List.drop(9223372036854775807, List.drop(9223372036854775807, " + SPLIT + "))")) {
            String report = report("List.any(t -> String.matches(\"[A-Z]{2}[0-9]\", t), "
                    + window + ")", "");
            assertFalse(report.contains("is divided by"), () -> window + "\n" + report);
            assertTrue(report.contains("not read: fork"), () -> window + "\n" + report);
        }
    }

    /**
     * A window whose language is more than the compiler will build is said to be: the position
     * is not divided for want of the work, which is not the position being divided no way.
     */
    @Test
    void aWindowTooLargeToDivideByIsSaidToBeTooLarge() {
        String report = report("List.any(t -> String.matches(\"[A-Z]{2}[0-9]\", t), "
                + "List.drop(2000000000, " + SPLIT + "))", "");
        assertFalse(report.contains("is divided by"), report);
        assertTrue(report.contains("more than this compiler will work out"), report);
    }

    /**
     * Some of none of the pieces meets a statement never, and every one of none does: a window of
     * none is read, and the condition is the constant it comes to — one decision, divided on
     * nothing, where a condition left unread is a fork nobody read. The rows hold at run time, so
     * the constants are the ones the run gives.
     */
    @Test
    void aWindowOfNoneIsReadAndTheConditionIsTheConstantItComesTo() {
        String pattern = "String.matches(\"[A-Z]{2}[0-9]\", t)";
        for (String window : List.of("List.take(0, " + SPLIT + ")",
                "List.drop(1, List.take(1, " + SPLIT + "))")) {
            String none = report("List.any(t -> " + pattern + ", " + window + ")", """

                    example hasCode
                        | "a code" : (Codes("AB7")) -> false
                    """);
            assertFalse(none.contains("not read: fork"), () -> window + "\n" + none);
            assertTrue(none.contains("decision    rules 1   taken 1"), () -> window + "\n" + none);
            assertFalse(none.contains("is divided by"), () -> window + "\n" + none);
            String every = report("List.all(t -> " + pattern + ", " + window + ")", """

                    example hasCode
                        | "nothing" : (Codes("")) -> true
                    """);
            assertFalse(every.contains("not read: fork"), () -> window + "\n" + every);
            assertTrue(every.contains("decision    rules 1   taken 1"), () -> window + "\n" + every);
            assertFalse(every.contains("is divided by"), () -> window + "\n" + every);
        }
    }

    /**
     * Pieces wrapped in a newtype before they are held to a predicate are the pieces: the window
     * is found beneath the wrapping as it is where there is none.
     */
    @Test
    void piecesWrappedInANewtypeAreDividedWhereTheyStand() {
        for (String window : List.of(SPLIT, "List.drop(1, " + SPLIT + ")")) {
            String condition = "List.any(c -> String.matches(\"[A-Z]{2}[0-9]\", c.value), "
                    + "List.map(t -> Code(t), " + window + "))";
            List<String> rows = offeredFor(measured(model(condition, "data Code = String")), A_CODE);
            assertEquals(2, rows.size(), () -> window + ": " + rows);
            Predicate<String> holds = text -> Strings.split(text, ";").stream()
                    .skip(window.equals(SPLIT) ? 0 : 1)
                    .anyMatch(piece -> Pattern.matches("[A-Z]{2}[0-9]", piece));
            assertNotEquals(holds.test(rows.get(0)), holds.test(rows.get(1)),
                    () -> window + ": two rows of one side: " + rows);
        }
    }

    /**
     * What the type itself holds the strings to is met with: a type of letters and separators has
     * no string with a piece of letters and a digit, so that side is no class and no row is offered
     * for it, and every row is one the type admits.
     */
    @Test
    void aSideTheTypesOwnPatternLeavesNoStringOnIsNoClass() {
        List<String> rows = offeredFor(measured(model(SOME_CODE, """
                    invariant String.matches("[A-Z;]*", value)
                """)), A_CODE);
        assertFalse(rows.isEmpty(), "rows are offered for what the type admits");
        for (String row : rows) {
            assertTrue(Pattern.matches("[A-Z;]*", row) && !conditions().get(
                            "SOME piece matches, all").ofTheString().test(row),
                    () -> "a row of the type that is on the side no string is on: " + rows);
        }
    }

    private static final String WITH_A_NUMBER = """
            module example.codes

            data Codes = { n: Int, s: String }

            behavior hasCode : (list: Codes) -> Int
            let hasCode (list) = if list.n > 5 then (if %s then 2 else 1) else 0

            example hasCode
                | "low" : (Codes { n = 0, s = "" }) -> 0
                | "high, none" : (Codes { n = 9, s = "" }) -> 1
                | "high, some" : (Codes { n = 9, s = "AB7" }) -> 2
            """;

    /**
     * A condition on the pieces beside a comparison leaves the obligations of the comparison as
     * they are, and divides the string as the same condition on the whole string does: the report
     * is the one the condition written of the string gives, but for the name of the rule. The
     * obligations that stood before the rule was read as the pieces are the ones that stand after.
     */
    @Test
    void theObligationsBesideAreTheOnesTheConditionOnTheWholeStringLeaves() {
        // Without what the rewrites came to: the pieces are walked, and a walk is rewritten where
        // the whole string is not, which is the replacement measure's and no obligation of the
        // comparison's.
        Function<String, String> reported = condition -> {
            Compilation compilation = measured(WITH_A_NUMBER.formatted(condition));
            return AdequacyReport.of(compilation)
                    .human(SourceRendering.namedByIdentity(compilation.texts()))
                    .replaceAll("predicate@\\d+:\\d+", "predicate")
                    .replaceAll("`list\\.s: [^`]*`", "`list.s: the rule`")
                    .lines()
                    .filter(line -> !line.strip().startsWith("replacement ")
                            && !line.contains("no row would come out differently if the fold")
                            && !line.startsWith("adequacy:")
                            && !line.matches("\\d+ gaps? marked .*"))
                    .collect(Collectors.joining("\n"));
        };
        String ofThePieces = reported.apply(
                "List.any(t -> String.matches(\"[A-Z]{2}[0-9]\", t), String.split(\";\", list.s))");
        String ofTheWhole = reported.apply("String.matches(\"[A-Z]{2}[0-9]\", list.s)");
        assertEquals(ofTheWhole, ofThePieces);
        assertTrue(ofThePieces.contains("equivalence partitions 4/4"), ofThePieces);
    }
}
