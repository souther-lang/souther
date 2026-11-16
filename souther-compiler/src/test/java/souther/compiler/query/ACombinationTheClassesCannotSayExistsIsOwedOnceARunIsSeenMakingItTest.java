package souther.compiler.query;

import souther.compiler.ACompiledModel;
import souther.compiler.reading.Condition;
import souther.compiler.report.AdequacyReport;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.fail;

/**
 * Whether a combination the classes do not state is owed a row is answered by a row: one a search
 * composed and a run was seen making it with. Until then the combination is counted and a finding
 * says it is open, and nothing is refused over it. One whose decisions state relations no value
 * holds together has no row to write: it is counted and is nobody's work, so it is no finding.
 */
class ACombinationTheClassesCannotSayExistsIsOwedOnceARunIsSeenMakingItTest {

    private static Compilation measured(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        ACompiledModel.compiles(compilation);
        return compilation;
    }

    private static List<Adequacy.Finding> findingsOf(String model, String module) {
        return findingsOf(measured(model), module);
    }

    private static List<Adequacy.Finding> findingsOf(Compilation compilation, String module) {
        return compilation.db().ask(new Adequacy.Findings(module)).value().stream()
                .filter(each -> each.about() instanceof About.ACombinationNoRowMakes).toList();
    }

    /**
     * Which combination a finding is about, said by the way each decision comes out, the decisions
     * taken in the order the body writes them: {@code 01} is the first failing and the second
     * holding. Never by how many findings there are, which two different combinations share.
     */
    private static String combinationOf(Adequacy.Finding finding) {
        About.ACombinationNoRowMakes about = (About.ACombinationNoRowMakes) finding.about();
        Map<Integer, Integer> byOrdinal = new TreeMap<>();
        for (Condition each : about.combination().settled()) {
            switch (each) {
                // A comparison coming out one way.
                case Condition.Side side -> byOrdinal.put(side.statedAt().origin().ordinal(),
                        side.held() ? 1 : 0);
                // An arm of a fork, the first arm being the one taken on holding.
                case Condition.Arm arm -> byOrdinal.put(arm.arm().fork().origin().ordinal(),
                        arm.arm().part() == 0 ? 1 : 0);
                case Condition.Case _ -> fail("a decision is a comparison or an arm: " + each);
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
        // twenty and of sixty-five or over, which no value is: it is no finding at all.
        assertEquals(Set.of("00", "11"), combinationsWhere(findings, true),
                () -> "a run is seen making the two a value holds: " + findings);
        assertEquals(Set.of(), combinationsWhere(findings, false),
                () -> "and the one no value holds is not left open, nor offered a row: "
                        + findings);
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
     * than the date. What the numbers say of the two years does not rule it out, so the
     * combinations that need it are not shown to have no row: they stay open, and none is offered.
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

    /**
     * A decision that holds on an age or on a case of a record is two ways of holding, and a
     * combination that needs the age to be of seventy-five or over with neither of them is held
     * by none, however the two decisions are written.
     */
    @Test
    void aCombinationNeitherWayOfAnAlternativeHoldsIsNoFinding() {
        Compilation compilation = measured("""
                module example.dep

                data Revenue = Int
                data Cover = Disabled | NotDisabled
                data Person = { birthday: Date, cover: Cover }
                data Reason = Old | Over

                let isDisabled (c: Cover): Bool =
                    match c with
                        | Disabled    -> true
                        | NotDisabled -> false

                let ageOn (birthday: Date, on: Date): Int =
                    Date.year(on) - Date.year(birthday)
                        - (if Date.month(on) * 100 + Date.day(on)
                              < Date.month(birthday) * 100 + Date.day(birthday)
                           then 1 else 0)

                let attainedAgeOn (birthday: Date, on: Date): Int =
                    ageOn(Date.addDays(0 - 1, birthday), on)

                let ceiling (person: Person, on: Date): Revenue =
                    if attainedAgeOn(person.birthday, on) >= 60 || isDisabled(person.cover)
                    then Revenue(18) else Revenue(13)

                let blockers (person: Person, revenue: Revenue, on: Date): List<Reason> =
                       [ Old | attainedAgeOn(person.birthday, on) >= 75 ]
                    ++ [ Over | revenue >= ceiling(person, on) ]

                behavior q : (person: Person, revenue: Revenue, on: Date) -> Int

                let q (person, revenue, on) =
                    List.length(blockers(person, revenue, on)) + ceiling(person, on).value

                example q
                    | (Person { birthday = Date("1990-01-01"), cover = NotDisabled },
                       Revenue(5), Date("2000-01-01")) -> 13
                """);
        List<Adequacy.Finding> findings = findingsOf(compilation, "example.dep");

        // Said by the decisions in the order the body states them (the ceiling, the age of
        // seventy-five, the revenue), the two the age of seventy-five makes with a ceiling of
        // neither sixty nor disabled are no combination: "010" and "011".
        assertEquals(Set.of("111", "101", "110", "100", "001", "11", "01", "10"),
                combinationsWhere(findings, true),
                () -> "each other one is made by a row a run is seen making it with: " + findings);
        assertEquals(Set.of(), combinationsWhere(findings, false),
                () -> "and the two none holds are not left open: " + findings);

        // And the page says what the findings say: the choices no row makes are the ones the
        // measure raised a finding of, and the two none holds are not among them.
        int said = AdequacyReport.of(compilation).modules().getFirst().behaviors().getFirst()
                .unobserved().stream().flatMap(group -> group.choices().stream())
                .mapToInt(AdequacyReport.UnobservedChoices::count).sum();
        assertEquals(findings.size(), said,
                () -> "the page names the combinations the findings name, and no more");
    }

    /**
     * A comparison coming out one way asks a row to be on that side of it and nowhere in
     * particular, so another decision on the same number puts the row at a value on that side
     * wherever it asks: at or over a limit, and under another value, is a number between them.
     */
    @Test
    void aCombinationOfAComparisonWithANumberAndOneWithAnotherValueIsOfferedARow() {
        List<Adequacy.Finding> findings = findingsOf("""
                module example.limit

                behavior fee : (x: Int, y: Int) -> Int

                let fee (x, y) =
                    (if x >= 13 then 10 else 20) + (if x >= y then 1 else 2)

                example fee
                    | (5, 1) -> 21
                """, "example.limit");

        // "10" is at the limit and under the other value, which asks the other value over it.
        assertEquals(Set.of("00", "10", "11"), combinationsWhere(findings, true),
                () -> "each the row did not make is made by a row a run is seen making it with: "
                        + findings);
        assertEquals(Set.of(), combinationsWhere(findings, false),
                () -> "and none is left open: " + findings);
    }
}
