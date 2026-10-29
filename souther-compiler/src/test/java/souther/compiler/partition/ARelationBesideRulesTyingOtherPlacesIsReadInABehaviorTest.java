package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.TestDay;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadings;
import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.OfferingRequest;
import souther.compiler.query.ReadAs;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.NavigableSet;
import java.util.Set;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comparison in a behavior over a number of a record is read beside a rule of the record tying
 * other places of it together, however the rule is written.
 *
 * <p>The behavior's half of what {@code check.ARuleTyingOtherPlacesTogetherWithholdsNothing
 * BesideThemTest} asks of the record's reading: the line the comparison draws is read, and one
 * clause of two parts says what the same two parts written as two clauses say. A part tying the
 * strings to the number withholds the line, as it should.
 */
class ARelationBesideRulesTyingOtherPlacesIsReadInABehaviorTest {

    private static Compilation measured(String rules) {
        Compilation compilation = Compilation.ofSource("""
                module demo

                data Yen = Int
                    invariant value >= 0

                data Priced = { total: Yen, subtotal: Yen, a: String, b: String, c: String }
                    invariant total.value <= subtotal.value
                %s

                behavior f : (p: Priced, cap: Int) -> Bool
                let f (p, cap) = p.total.value <= cap
                """.formatted(rules), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    /** What is said of the relations of the behavior, apart from the rest of a report. */
    private static NavigableSet<String> aboutTheRelation(Compilation compilation) {
        NavigableSet<String> out = new TreeSet<>();
        Matcher found = Pattern.compile("\"reason\"\\s*:\\s*\"(relation_[a-z_]+)\"").matcher(
                AdequacyReport.of(compilation)
                        .json(SourceRendering.namedByIdentity(SourceLayouts.NONE)));
        while (found.find()) {
            out.add(found.group(1));
        }
        return out;
    }

    /** The classes each axis of the behavior is parted into. */
    private static Map<String, List<String>> classes(Compilation compilation) {
        Map<String, List<String>> out = new LinkedHashMap<>();
        compilation.db().ask(new Adequacy.Coverage("demo")).value().get("f").axes()
                .forEach(axis -> out.put(axis.path(), axis.classes()));
        return out;
    }

    @Test
    void theLineIsReadBesideARuleOverTwoStringsWrittenEitherWay() {
        Compilation bare = measured("");
        Compilation apart = measured("""
                    invariant String.contains(a, b)
                    invariant String.contains("q", c)
                """);
        Compilation joined = measured(
                "    invariant String.contains(a, b) && String.contains(\"q\", c)");

        assertFalse(aboutTheRelation(apart).contains("relation_not_shown_to_reach_every_value"),
                () -> aboutTheRelation(apart).toString());
        assertEquals(classes(bare), classes(apart), "the strings part the total no differently");
        assertEquals(aboutTheRelation(apart), aboutTheRelation(joined),
                "one clause of two parts says what two clauses do");
        assertEquals(classes(apart), classes(joined));
    }

    /**
     * And a row is written on each side of the line, under rules on the record's strings however
     * they are written.
     *
     * <p>A row is chosen a position at a time, and a string position took the strings of its type:
     * under a pattern the record states on it, or a rule relating it to another string, every row
     * was refused and the line had none. A position offers the strings its rules admit, and the
     * strings a rule ties together are offered as the one value of them the rules were shown to
     * hold of.
     */
    @Test
    void aRowIsWrittenOnEachSideOfTheLine() {
        for (String rules : List.of(
                "    invariant String.matches(\"[A-Z]+\", a)",
                "    invariant String.contains(a, b)\n    invariant String.contains(\"q\", c)",
                "    invariant String.contains(a, b) && String.contains(\"q\", c)",
                "    invariant String.contains(\"q\", a) && String.contains(a, b)")) {
            Compilation measured = measured(rules);
            List<int[]> rows = rowsOffered(measured);

            assertTrue(rows.stream().anyMatch(row -> row[0] <= row[1]),
                    () -> rules + ": a row where the total is within the cap " + offered(measured));
            assertTrue(rows.stream().anyMatch(row -> row[0] > row[1]),
                    () -> rules + ": a row where it is past it " + offered(measured));
        }
    }

    /** And a value of the record alone is the one value of the strings tied together. */
    @Test
    void aValueOfTheRecordHoldsTheStringsTiedTogether() {
        Compilation compilation = Compilation.ofSource("""
                module demo

                data Priced = { total: Int, a: String, b: String }
                    invariant String.contains("q", a) && String.contains(a, b)
                """, "Main");
        String module = compilation.modules().get(0);
        RuleReadingContext reading = RuleReadingContext.unshared(
                RuleReadings.of(compilation, module), ReadAs.THE_COMPILATION_DOES, TestDay.TODAY);

        assertEquals(List.of("Priced { total = 0, a = \"q\", b = \"q\" }"),
                Partitions.representativesOf(
                                Type.ref(TypeSymbols.declared(new TypeKey(module, "Priced"))),
                                reading)
                        .values().stream().map(FixtureTemplate::text).toList());
    }

    private static final String PAIR = """
            module demo

            data Pair = { a: String, b: String }
                invariant String.contains(a, b) && String.length(b) <= 2
            """;

    /**
     * A value of the strings tied together is one value of both, so a field given beside it is
     * given to the value and not set beside a part of another.
     *
     * <p>With nothing given, an empty {@code a} and an empty {@code b} hold the rule; with
     * {@code a} given as {@code "xy"}, the empty {@code b} of that value holds nothing, and the
     * {@code b} written is one the rule holds of beside the {@code a} given.
     */
    @Test
    void aFieldGivenIsHeldInTheValueOfTheStringsTiedToIt() {
        Compilation compilation = Compilation.ofSource(PAIR, "Main");
        String module = compilation.modules().get(0);
        RuleReadingContext reading = RuleReadingContext.unshared(
                RuleReadings.of(compilation, module), ReadAs.THE_COMPILATION_DOES, TestDay.TODAY);
        TypeSymbol.AtModule pair = TypeSymbols.declared(new TypeKey(module, "Pair"));

        assertEquals(List.of("Pair { a = \"xy\", b = \"xy\" }"),
                Partitions.composed(pair, pair, reading, Set.of(),
                                Map.of("a", FixtureTemplate.string("xy")),
                                Partitions.RulesAround.NONE)
                        .values().stream().map(FixtureTemplate::text).toList());
    }

    /**
     * And a row whose assignment puts a class of a string at one of the strings tied together is
     * written with the other held to it: the value the other was offered was found with nothing
     * settled, and beside the class the row stands at it holds nothing.
     */
    @Test
    void aRowAtAClassOfOneStringIsWrittenWithTheOtherHeldToIt() {
        Compilation compilation = Compilation.ofSource(PAIR + """

                behavior f : (p: Pair) -> Bool
                let f (p) = p.a == "xy"
                """, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String rows = offered(compilation);

        assertTrue(rows.contains("Pair { a = \"xy\", b = \"xy\" }"),
                () -> "a row at the class of `a` the comparison draws: " + rows);
    }

    /**
     * A row written with the strings tied together lands in the classes it says it fills, and the
     * classes an axis decides are filled where a value the rules hold of is in them.
     *
     * <p>Which classes a row stands in is read off its values, so a row is never said to fill a
     * class its values are outside. What is asked here is the other half: the class of {@code a}
     * at {@code "A"} beside {@code b} away from {@code "B"} has a row, though the value the search
     * put at {@code b} for that class holds no {@code "A"}. And the comparison of {@code b} is
     * reached only where {@code a} is {@code "A"}, where no {@code b} of {@code "B"} holds the
     * rule, so no row is said to be on it.
     */
    @Test
    void aRowLandsInTheClassesItSaysItFills() {
        Compilation compilation = measuredRows("""
                module demo

                data Pair = { a: String, b: String }
                    invariant String.matches("[AB]", a)
                    invariant String.contains(a, b)

                behavior f : (p: Pair) -> Bool
                let f (p) = p.a == "A" && p.b == "B"
                """);
        List<String[]> rows = pairsOffered(compilation);

        assertTrue(rows.stream().anyMatch(row -> row[0].equals("A") && !row[1].equals("B")),
                () -> "a row at `a` of \"A\" and `b` away from \"B\": " + offered(compilation));
        assertFalse(offered(compilation).contains("no row for `p.a== A`"),
                () -> "and the class of `a` at \"A\" is one of those it fills: "
                        + offered(compilation));
        assertTrue(rows.stream().allMatch(row -> row[1].contains(row[0])),
                () -> "every row holds the rule: " + offered(compilation));
    }

    /**
     * And a row at a value an axis decides is written with that value held, and the strings tied
     * to it written beside it.
     *
     * <p>{@code b} is one character at most and holds {@code a}, so it is {@code a}. The row at
     * {@code a} of {@code "B"} has {@code b} written as {@code "B"}: a value of the two found with
     * nothing held is the first one tried, at {@code "A"}, and a row written with it stands at
     * another class.
     */
    @Test
    void aRowAtAValueAnAxisDecidesHoldsItAndWritesTheRestBesideIt() {
        Compilation compilation = measuredRows("""
                module demo

                data Pair = { a: String, b: String }
                    invariant String.matches("[AB]", a)
                    invariant String.contains(a, b) && String.length(b) <= 1

                behavior f : (p: Pair) -> Bool
                let f (p) = p.a == "B"
                """);

        assertTrue(pairsOffered(compilation).stream()
                        .anyMatch(row -> row[0].equals("B") && row[1].equals("B")),
                () -> "a row at `a` of \"B\": " + offered(compilation));
    }

    private static Compilation measuredRows(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    /** The {@code a} and {@code b} of each pair offered as a row. */
    private static List<String[]> pairsOffered(Compilation compilation) {
        List<String[]> out = new ArrayList<>();
        Matcher row = Pattern.compile("Pair \\{ a = \"([^\"]*)\", b = \"([^\"]*)\" }")
                .matcher(offered(compilation));
        while (row.find()) {
            out.add(new String[] {row.group(1), row.group(2)});
        }
        return out;
    }

    private static String offered(Compilation compilation) {
        return GeneratedRows.of(
                Adequacy.offeredFor(compilation.db(), OfferingRequest.overTheModule("demo")),
                Map.of(), SourceRendering.namedByIdentity(compilation.texts()), compilation.db())
                .text();
    }

    /** The total and the cap of each row offered. */
    private static List<int[]> rowsOffered(Compilation compilation) {
        List<int[]> out = new ArrayList<>();
        Matcher row = Pattern.compile("total = Yen\\((-?\\d+)\\)[^}]*}, (-?\\d+)\\)")
                .matcher(offered(compilation));
        while (row.find()) {
            out.add(new int[] {Integer.parseInt(row.group(1)), Integer.parseInt(row.group(2))});
        }
        return out;
    }

    @Test
    void butNotBesideAPartTyingTheStringsToTheNumber() {
        Compilation tied = measured("""
                    invariant String.contains(a, b)
                    invariant String.length(b) <= total.value
                """);

        assertTrue(aboutTheRelation(tied).contains("relation_not_shown_to_reach_every_value"),
                () -> aboutTheRelation(tied).toString());
    }
}
