package souther.compiler.query;

import souther.compiler.ACompiledModel;

import org.junit.jupiter.api.Test;

import java.util.List;

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
        assertEquals(2, findings.size(), () -> "the combinations the row did not make: " + findings);
        assertTrue(findings.stream().allMatch(Adequacy.Finding::established),
                () -> "and a run is seen making each of them, so each is owed a row: " + findings);
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

        // Of the three the example's row did not make, two are an age under twenty and an age of
        // sixty-five or over, each of which a row is composed for. The third is an age under
        // twenty and of sixty-five or over, which no row is, and stays open.
        assertEquals(2, findings.stream().filter(Adequacy.Finding::established).count(),
                () -> "a run is seen making the two a value holds: " + findings);
        assertEquals(1, findings.stream().filter(each -> !each.established()).count(),
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

        assertEquals(3, findings.size(), () -> "the combinations the row did not make: " + findings);
        assertTrue(findings.stream().allMatch(Adequacy.Finding::established),
                () -> "each is made by a row a run is seen making it with: " + findings);
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

        assertEquals(2, findings.stream().filter(each -> !each.established()).count(),
                () -> "the two that need the day before to fall in a later year: " + findings);
    }
}
