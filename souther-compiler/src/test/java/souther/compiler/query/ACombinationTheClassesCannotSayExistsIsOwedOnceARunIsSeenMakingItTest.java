package souther.compiler.query;

import souther.compiler.ACompiledModel;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Whether a combination the classes do not state is owed a row is answered by a row: one a search
 * composed and a run was seen making it with. Until then the combination is counted and a finding
 * says it is open, and nothing is refused over it. One whose decisions state relations no value
 * holds together is no combination at all.
 */
class ACombinationTheClassesCannotSayExistsIsOwedOnceARunIsSeenMakingItTest {

    private static List<Adequacy.Finding> findingsOf(String model, String module) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        ACompiledModel.compiles(compilation);
        return compilation.db().ask(new Adequacy.Findings(module)).value().stream()
                .filter(each -> each.about() instanceof About.ACombinationNoRowMakes).toList();
    }

    /** A comparison coming out one way: {@code x fails at …ordinal=1…}. */
    private static final Pattern COMPARISON = Pattern.compile("(holds|fails) at .*?ordinal=(\\d+)");

    /** An arm of a fork: {@code …ordinal=0…]/0}, the first arm being the one taken on holding. */
    private static final Pattern ARM = Pattern.compile("ordinal=(\\d+)[^\\]]*\\]/(\\d)");

    /**
     * Which combination a finding is about, said by the way each decision comes out, the decisions
     * taken in the order the body writes them: {@code 01} is the first failing and the second
     * holding. Never by how many findings there are, which two different combinations share.
     */
    private static String combinationOf(Adequacy.Finding finding) {
        About.ACombinationNoRowMakes about = (About.ACombinationNoRowMakes) finding.about();
        Map<Integer, Integer> byOrdinal = new TreeMap<>();
        for (Object each : about.combination().settled()) {
            Matcher comparison = COMPARISON.matcher(each.toString());
            Matcher arm = ARM.matcher(each.toString());
            if (comparison.find()) {
                byOrdinal.put(Integer.parseInt(comparison.group(2)),
                        comparison.group(1).equals("holds") ? 1 : 0);
            } else {
                assertTrue(arm.find(), () -> "a decision says which construct and which way: " + each);
                byOrdinal.put(Integer.parseInt(arm.group(1)), arm.group(2).equals("0") ? 1 : 0);
            }
        }
        return byOrdinal.values().stream().map(String::valueOf).collect(Collectors.joining());
    }

    /** The combinations among {@code findings} that are {@code established}, or are not. */
    private static Set<String> combinationsWhere(List<Adequacy.Finding> findings,
                                                  boolean established) {
        return findings.stream().filter(each -> each.established() == established)
                .map(ACombinationTheClassesCannotSayExistsIsOwedOnceARunIsSeenMakingItTest::combinationOf)
                .collect(Collectors.toCollection(TreeSet::new));
    }

    /** A relation two rows can each be written for, so a run is seen making each. */
    @Test
    void aCombinationARunIsSeenMakingIsAGapAndOneNoValueHoldsIsNoCombination() {
        List<Adequacy.Finding> findings = findingsOf("""
                module example.fee

                behavior fee : (x: Int, y: Int) -> Int

                let fee (x, y) =
                    (if x == y then 10 else 20) + (if x > y then 1 else 2)

                example fee
                    | (1, 2) -> 22
                """, "example.fee");

        // x == y with x > y is no combination: the relations the two decisions state leave no
        // value, so it is not asked for. Of the three left, the row made one.
        assertEquals(Set.of("01", "10"), combinationsWhere(findings, true),
                () -> "a run is seen making each of the two left, so each is owed a row: " + findings);
        assertEquals(Set.of(), combinationsWhere(findings, false),
                () -> "and none of them is left open: " + findings);
    }

    /**
     * Decisions that compare a number taken of two values with a written one are in no class of
     * either, so the cell they are looked for in is every row. A row for them is composed at
     * values that meet the relations the decisions state, and a run is seen making the
     * combination.
     */
    @Test
    void aCombinationOfDecisionsOnANumberTakenOfTwoValuesIsOfferedARowThatMeetsThem() {
        List<Adequacy.Finding> findings = findingsOf("""
                module example.age

                behavior fee : (birthday: Date, on: Date) -> Int

                let fee (birthday, on) =
                    (if Date.year(on) - Date.year(birthday) >= 20 then 10 else 20)
                    + (if Date.year(on) - Date.year(birthday) >= 65 then 1 else 2)

                example fee
                    | (Date("2000-01-01"), Date("2030-01-01")) -> 12
                """, "example.age");

        // Of the three the example's row did not make, "11" is an age of sixty-five or over and
        // "00" an age under twenty, each of which a row is composed for. "01" is an age under
        // twenty and of sixty-five or over, which no row is, and stays open.
        assertEquals(Set.of("00", "11"), combinationsWhere(findings, true),
                () -> "a run is seen making the two a value holds: " + findings);
        assertEquals(Set.of("01"), combinationsWhere(findings, false),
                () -> "and the one no value holds is not offered a row: " + findings);
    }

    /**
     * Two numbers taken of one date are one date's: a row for the year before a birthday differing
     * from the year of it is a birthday on the first of a year, and is composed as one.
     */
    @Test
    void twoNumbersTakenOfOneDateAreComposedAsOneDate() {
        List<Adequacy.Finding> findings = findingsOf("""
                module example.age

                behavior fee : (birthday: Date, on: Date) -> Int

                let fee (birthday, on) =
                    (if Date.year(Date.addDays(0 - 1, birthday)) < Date.year(birthday)
                     then 10 else 20)
                    + (if Date.year(on) - Date.year(birthday) >= 20 then 1 else 2)

                example fee
                    | (Date("2000-06-01"), Date("2030-01-01")) -> 21
                """, "example.age");

        assertEquals(Set.of("00", "10", "11"), combinationsWhere(findings, true),
                () -> "each the row did not make is made by a row a run is seen making it with: "
                        + findings);
        assertEquals(Set.of(), combinationsWhere(findings, false),
                () -> "and none of them is left open: " + findings);
    }

    /**
     * A relation no date meets is not met by a row: the day before a date is never in a later year
     * than the date, so the combinations that need it stay open and no row is offered for them.
     */
    @Test
    void aRelationNoDateMeetsIsOfferedNoRow() {
        List<Adequacy.Finding> findings = findingsOf("""
                module example.age

                behavior fee : (birthday: Date, on: Date) -> Int

                let fee (birthday, on) =
                    (if Date.year(Date.addDays(0 - 1, birthday)) > Date.year(birthday)
                     then 10 else 20)
                    + (if Date.year(on) - Date.year(birthday) >= 20 then 1 else 2)

                example fee
                    | (Date("2000-06-01"), Date("2030-01-01")) -> 21
                """, "example.age");

        assertEquals(Set.of("10", "11"), combinationsWhere(findings, false),
                () -> "the two that need the day before to fall in a later year: " + findings);
        assertEquals(Set.of("00"), combinationsWhere(findings, true),
                () -> "and the one that does not is made: " + findings);
    }
}
