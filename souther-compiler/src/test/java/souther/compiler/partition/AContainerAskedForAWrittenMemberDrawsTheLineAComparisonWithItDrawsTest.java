package souther.compiler.partition;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.numeric.Text;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ItemAssessment;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.concurrent.ConcurrentHashMap;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A container asked for a member the source wrote is asked of its elements what a comparison of
 * them with that value is: the line is at the value, a row at it holds the value, and a row on
 * either side holds an element below it or above it. A member that is another place of the row
 * is a relation of two values and draws none.
 */
class AContainerAskedForAWrittenMemberDrawsTheLineAComparisonWithItDrawsTest {

    private static final Map<String, Compilation> MEASURED = new ConcurrentHashMap<>();

    private static final String MODEL = """
            module probe
            data Group = { tags: List<String>, n: Int, nums: List<Int> }
            data Line = { code: String, rates: Map<String, Int>, rates2: Map<String, Int>,
                          tags: List<String>,
                          ids: Set<String>, nums: List<Int>, days: List<Date>, n: Int,
                          other: List<String>, groups: List<Group>, s: String, i: Int,
                          times: List<Time>, instants: List<Instant>, ats: List<DateTime>,
                          emo: List<String>, dated: Map<Date, Int>, byTime: Map<Time, Int> }

            behavior nested : (l: Line) -> Bool
            let nested (l) = List.any(g -> g.n > 3 && List.contains("K", g.tags), l.groups)
            behavior nestedD : (l: Line) -> Bool
            let nestedD (l) = List.any(g -> g.n > 3 && List.contains(g.n + 1, g.nums), l.groups)
            behavior nestedDAny : (l: Line) -> Bool
            let nestedDAny (l) =
                List.any(g -> g.n > 3 && List.any(e -> e == g.n + 1, g.nums), l.groups)
            behavior nestedFirst : (l: Line) -> Bool
            let nestedFirst (l) = List.any(g -> List.contains("K", g.tags) && g.n > 3, l.groups)
            behavior nestedFirstAny : (l: Line) -> Bool
            let nestedFirstAny (l) =
                List.any(g -> List.any(t -> t == "K", g.tags) && g.n > 3, l.groups)
            behavior nestedAny : (l: Line) -> Bool
            let nestedAny (l) =
                List.any(g -> g.n > 3 && List.any(t -> t == "K", g.tags), l.groups)

            behavior exactlyOne : (l: Line) -> Bool
            let exactlyOne (l) =
                List.length(List.filter(b -> b,
                    [List.contains("K", l.tags), List.contains("L", l.tags)])) == 1
            behavior exactlyOneAny : (l: Line) -> Bool
            let exactlyOneAny (l) =
                List.length(List.filter(b -> b,
                    [List.any(t -> t == "K", l.tags), List.any(t -> t == "L", l.tags)])) == 1

            behavior combined : (l: Line) -> Int
            let combined (l) = if (List.contains("K", l.tags) && l.n > 3) == true then 1 else 0
            behavior combinedAny : (l: Line) -> Int
            let combinedAny (l) =
                if (List.any(t -> t == "K", l.tags) && l.n > 3) == true then 1 else 0
            behavior hasTime : (l: Line) -> Bool
            let hasTime (l) = List.contains(Time("09:00"), l.times)
            behavior anyTime : (l: Line) -> Bool
            let anyTime (l) = List.any(e -> e == Time("09:00"), l.times)
            behavior hasInstant : (l: Line) -> Bool
            let hasInstant (l) = List.contains(Instant("2026-07-25T00:00:00Z"), l.instants)
            behavior anyInstant : (l: Line) -> Bool
            let anyInstant (l) = List.any(e -> e == Instant("2026-07-25T00:00:00Z"), l.instants)
            behavior hasAt : (l: Line) -> Bool
            let hasAt (l) = List.contains(DateTime("2026-07-25T09:00"), l.ats)
            behavior anyAt : (l: Line) -> Bool
            let anyAt (l) = List.any(e -> e == DateTime("2026-07-25T09:00"), l.ats)
            behavior hasEmoji : (l: Line) -> Bool
            let hasEmoji (l) = List.contains("😀", l.emo)
            behavior anyEmoji : (l: Line) -> Bool
            let anyEmoji (l) = List.any(e -> e == "😀", l.emo)

            behavior ofWrittenList : (l: Line) -> Bool
            let ofWrittenList (l) = List.contains(l.s, ["A", "B"])
            behavior ofWrittenListAny : (l: Line) -> Bool
            let ofWrittenListAny (l) = List.any(e -> e == l.s, ["A", "B"])
            behavior ofWrittenSet : (l: Line) -> Bool
            let ofWrittenSet (l) = Set.contains(l.s, Set.fromList(["A", "B"]))
            behavior ofWrittenInts : (l: Line) -> Bool
            let ofWrittenInts (l) = List.contains(l.i, [10, 20, 30])
            behavior ofWrittenIntsAny : (l: Line) -> Bool
            let ofWrittenIntsAny (l) = List.any(e -> e == l.i, [10, 20, 30])

            behavior mapped : (l: Line) -> List<Bool>
            let mapped (l) = List.map(k -> List.contains(k, l.tags), ["K", "L"])
            behavior mappedAny : (l: Line) -> List<Bool>
            let mappedAny (l) = List.map(k -> List.any(t -> t == k, l.tags), ["K", "L"])
            behavior mixed : (l: Line) -> List<Bool>
            let mixed (l) = List.map(xs -> List.contains(l.s, xs), [[], ["K"]])
            behavior mixedAny : (l: Line) -> List<Bool>
            let mixedAny (l) = List.map(xs -> List.any(e -> e == l.s, xs), [[], ["K"]])

            behavior any : (l: Line) -> Bool
            let any (l) = List.any(t -> t == "K", l.tags)
            behavior listed : (l: Line) -> Bool
            let listed (l) = List.contains("K", l.tags)
            behavior setted : (l: Line) -> Bool
            let setted (l) = Set.contains("K", l.ids)
            behavior keyed : (l: Line) -> Bool
            let keyed (l) = Map.containsKey("USD", l.rates)
            behavior absent : (l: Line) -> Bool
            let absent (l) = Bool.not(List.contains("K", l.tags))
            behavior numbered : (l: Line) -> Bool
            let numbered (l) = List.contains(5, l.nums)
            behavior anyDay : (l: Line) -> Bool
            let anyDay (l) = List.any(d -> d == Date("2026-01-05"), l.days)
            behavior hasDay : (l: Line) -> Bool
            let hasDay (l) = List.contains(Date("2026-01-05"), l.days)
            behavior another : (l: Line) -> Bool
            let another (l) = Map.containsKey(l.code, l.rates)
            behavior listedKeys : (l: Line) -> Bool
            let listedKeys (l) = List.contains("USD", Map.keys(l.rates))
            behavior listedValues : (l: Line) -> Bool
            let listedValues (l) = List.contains(5, Map.values(l.rates))
            behavior anyKey : (l: Line) -> Bool
            let anyKey (l) = List.any(k -> k == "USD", Map.keys(l.rates))
            behavior anyValue : (l: Line) -> Bool
            let anyValue (l) = List.any(v -> v == 5, Map.values(l.rates))
            behavior anyDatedKey : (l: Line) -> Bool
            let anyDatedKey (l) = List.any(k -> k == Date("2026-01-05"), Map.keys(l.dated))
            behavior anotherListed : (l: Line) -> Bool
            let anotherListed (l) = List.contains(l.code, Map.keys(l.rates))
            behavior datedKey : (l: Line) -> Bool
            let datedKey (l) = Map.containsKey(Date("2026-01-05"), l.dated)
            behavior timedKey : (l: Line) -> Bool
            let timedKey (l) = Map.containsKey(Time("09:00"), l.byTime)

            behavior filteredNums : (l: Line) -> Bool
            let filteredNums (l) = List.contains(5, List.filter(x -> x > 3, l.nums))
            behavior filteredNumsAny : (l: Line) -> Bool
            let filteredNumsAny (l) = List.any(e -> e == 5, List.filter(x -> x > 3, l.nums))
            behavior filteredKeys : (l: Line) -> Bool
            let filteredKeys (l) =
                Map.containsKey("USD", Map.filterEntries((_, v) -> v > 3, l.rates))
            behavior filteredKeysAny : (l: Line) -> Bool
            let filteredKeysAny (l) =
                List.any(k -> k == "USD", Map.keys(Map.filterEntries((_, v) -> v > 3, l.rates)))
            behavior taken : (l: Line) -> Bool
            let taken (l) = List.contains("K", List.take(2, l.tags))
            behavior takenAny : (l: Line) -> Bool
            let takenAny (l) = List.any(t -> t == "K", List.take(2, l.tags))
            behavior dropped : (l: Line) -> Bool
            let dropped (l) = List.contains("K", List.drop(1, l.tags))
            behavior droppedAny : (l: Line) -> Bool
            let droppedAny (l) = List.any(t -> t == "K", List.drop(1, l.tags))
            behavior distinctTags : (l: Line) -> Bool
            let distinctTags (l) = List.contains("K", List.distinct(l.tags))
            behavior distinctTagsAny : (l: Line) -> Bool
            let distinctTagsAny (l) = List.any(t -> t == "K", List.distinct(l.tags))
            behavior removedKeys : (l: Line) -> Bool
            let removedKeys (l) = Map.containsKey("USD", Map.remove("EUR", l.rates))
            behavior removedKeysAny : (l: Line) -> Bool
            let removedKeysAny (l) =
                List.any(k -> k == "USD", Map.keys(Map.remove("EUR", l.rates)))
            behavior alongsideTaken : (l: Line) -> Int
            let alongsideTaken (l) =
                if List.contains("K", List.take(2, l.tags)) && l.n > 3 then 1 else 0
            behavior alongsideTakenAny : (l: Line) -> Int
            let alongsideTakenAny (l) =
                if List.any(t -> t == "K", List.take(2, l.tags)) && l.n > 3 then 1 else 0
            behavior eitherTaken : (l: Line) -> Int
            let eitherTaken (l) =
                if List.contains("K", List.take(2, l.tags))
                        || List.contains("M", List.drop(1, l.other)) then 1 else 0
            behavior eitherTakenAny : (l: Line) -> Int
            let eitherTakenAny (l) =
                if List.any(t -> t == "K", List.take(2, l.tags))
                        || List.any(t -> t == "M", List.drop(1, l.other)) then 1 else 0
            behavior mappedTaken : (l: Line) -> List<Bool>
            let mappedTaken (l) = List.map(k -> List.contains(k, List.take(2, l.tags)), ["K", "L"])
            behavior mappedTakenAny : (l: Line) -> List<Bool>
            let mappedTakenAny (l) =
                List.map(k -> List.any(t -> t == k, List.take(2, l.tags)), ["K", "L"])
            behavior removedItself : (l: Line) -> Bool
            let removedItself (l) = Map.containsKey("USD", Map.remove("USD", l.rates))
            behavior removedItselfAny : (l: Line) -> Bool
            let removedItselfAny (l) =
                List.any(k -> k == "USD", Map.keys(Map.remove("USD", l.rates)))
            behavior removedFromSet : (l: Line) -> Bool
            let removedFromSet (l) = Set.contains("K", Set.remove("Z", l.ids))
            behavior keptOfDistinct : (l: Line) -> Bool
            let keptOfDistinct (l) =
                List.contains(5, List.filter(x -> x > 3, List.distinct(l.nums)))
            behavior keptOfDistinctAny : (l: Line) -> Bool
            let keptOfDistinctAny (l) =
                List.any(e -> e == 5, List.filter(x -> x > 3, List.distinct(l.nums)))
            behavior keptAgainstTheValue : (l: Line) -> Bool
            let keptAgainstTheValue (l) =
                List.contains(2, List.filter(x -> x > 3, List.distinct(l.nums)))
            behavior keptAgainstTheValueWithoutIt : (l: Line) -> Bool
            let keptAgainstTheValueWithoutIt (l) =
                List.contains(2, List.filter(x -> x > 3, l.nums))
            behavior emptiedSet : (l: Line) -> Bool
            let emptiedSet (l) = Set.isEmpty(Set.remove("K", l.ids))
            behavior emptiedSetAny : (l: Line) -> Bool
            let emptiedSetAny (l) = Set.isEmpty(Set.filter(e -> e /= "K", l.ids))
            behavior emptiedMap : (l: Line) -> Bool
            let emptiedMap (l) = Map.isEmpty(Map.remove("USD", l.rates))
            behavior emptiedMapAny : (l: Line) -> Bool
            let emptiedMapAny (l) =
                Map.isEmpty(Map.filterEntries((k, _) -> k /= "USD", l.rates))
            behavior keysOfKept : (l: Line) -> Bool
            let keysOfKept (l) =
                List.contains("K", Map.keys(Map.filterEntries((_, v) -> v > 3, l.rates)))
            behavior keysOfKeptAny : (l: Line) -> Bool
            let keysOfKeptAny (l) =
                List.any(k -> k == "K", Map.keys(Map.filterEntries((_, v) -> v > 3, l.rates)))
            behavior valuesOfKept : (l: Line) -> Bool
            let valuesOfKept (l) =
                List.contains(5, Map.values(Map.filterEntries((_, v) -> v > 3, l.rates)))
            behavior valuesOfKeptAny : (l: Line) -> Bool
            let valuesOfKeptAny (l) =
                List.any(v -> v == 5, Map.values(Map.filterEntries((_, v) -> v > 3, l.rates)))
            behavior keysOfTaken : (l: Line) -> Bool
            let keysOfTaken (l) = List.contains("K", Map.keys(Map.remove("Z", l.rates)))
            behavior keysOfTakenAny : (l: Line) -> Bool
            let keysOfTakenAny (l) = List.any(k -> k == "K", Map.keys(Map.remove("Z", l.rates)))
            behavior valuesOfTaken : (l: Line) -> Bool
            let valuesOfTaken (l) = List.contains(5, Map.values(Map.remove("Z", l.rates)))
            behavior valuesOfTakenAny : (l: Line) -> Bool
            let valuesOfTakenAny (l) = List.any(v -> v == 5, Map.values(Map.remove("Z", l.rates)))
            behavior valuesOfIntersected : (l: Line) -> Bool
            let valuesOfIntersected (l) =
                List.contains(5, Map.values(Map.intersection(l.rates, l.rates2)))
            behavior valuesOfIntersectedAny : (l: Line) -> Bool
            let valuesOfIntersectedAny (l) =
                List.any(v -> v == 5, Map.values(Map.intersection(l.rates, l.rates2)))
            behavior keysOfRewritten : (l: Line) -> Bool
            let keysOfRewritten (l) =
                List.contains("K", Map.keys(Map.mapValues((_, v) -> v + 1, l.rates)))
            behavior keysOfRewrittenAny : (l: Line) -> Bool
            let keysOfRewrittenAny (l) =
                List.any(k -> k == "K", Map.keys(Map.mapValues((_, v) -> v + 1, l.rates)))
            behavior valuesOfRewritten : (l: Line) -> Bool
            let valuesOfRewritten (l) =
                List.contains(5, Map.values(Map.mapValues((_, v) -> v + 1, l.rates)))
            behavior valuesOfRewrittenAny : (l: Line) -> Bool
            let valuesOfRewrittenAny (l) =
                List.any(v -> v == 5, Map.values(Map.mapValues((_, v) -> v + 1, l.rates)))
            behavior distinctOfKept : (l: Line) -> Bool
            let distinctOfKept (l) =
                List.contains(5, List.distinct(List.filter(x -> x > 3, l.nums)))
            behavior distinctOfKeptAny : (l: Line) -> Bool
            let distinctOfKeptAny (l) =
                List.any(e -> e == 5, List.distinct(List.filter(x -> x > 3, l.nums)))
            behavior sortOfTaken : (l: Line) -> Bool
            let sortOfTaken (l) = List.contains("K", List.sort(List.take(2, l.tags)))
            behavior sortOfTakenAny : (l: Line) -> Bool
            let sortOfTakenAny (l) = List.any(t -> t == "K", List.sort(List.take(2, l.tags)))
            behavior takenOfSorted : (l: Line) -> Bool
            let takenOfSorted (l) = List.contains("K", List.take(2, List.sort(l.tags)))
            behavior takenOfSortedAny : (l: Line) -> Bool
            let takenOfSortedAny (l) = List.any(t -> t == "K", List.take(2, List.sort(l.tags)))
            behavior keptByRemainder : (l: Line) -> Bool
            let keptByRemainder (l) =
                List.contains(5, List.filter(x -> Int.floorMod(x, 2) == 1, l.nums))
            behavior keptByRemainderAny : (l: Line) -> Bool
            let keptByRemainderAny (l) =
                List.any(e -> e == 5, List.filter(x -> Int.floorMod(x, 2) == 1, l.nums))
            behavior chained : (l: Line) -> Bool
            let chained (l) = List.contains("K", List.take(3, List.distinct(l.tags)))
            behavior chainedAny : (l: Line) -> Bool
            let chainedAny (l) = List.any(t -> t == "K", List.take(3, List.distinct(l.tags)))
            behavior mappedMember : (l: Line) -> Bool
            let mappedMember (l) = List.contains("K", List.map(t -> String.trim(t), l.tags))
            behavior mappedMemberAny : (l: Line) -> Bool
            let mappedMemberAny (l) =
                List.any(t -> t == "K", List.map(t -> String.trim(t), l.tags))
            behavior anotherFiltered : (l: Line) -> Bool
            let anotherFiltered (l) = List.contains(l.s, List.distinct(l.other))
            behavior anotherTaken : (l: Line) -> Bool
            let anotherTaken (l) = List.contains(l.s, List.take(2, l.other))

            behavior guarded : (l: Line) -> Int
            let guarded (l) = if Map.containsKey("USD", l.rates) then 1 else 0
            behavior alongside : (l: Line) -> Int
            let alongside (l) = if List.contains("K", l.tags) && l.n > 3 then 1 else 0
            behavior alongsideAny : (l: Line) -> Int
            let alongsideAny (l) = if List.any(t -> t == "K", l.tags) && l.n > 3 then 1 else 0
            behavior either : (l: Line) -> Int
            let either (l) = if List.contains("K", l.tags) || List.contains("M", l.other) then 1 else 0
            behavior eitherAny : (l: Line) -> Int
            let eitherAny (l) = if List.any(t -> t == "K", l.tags) || List.any(t -> t == "M", l.other) then 1 else 0
            behavior inEachGroup : (l: Line) -> Bool
            let inEachGroup (l) = List.all(g -> List.contains("K", g.tags), l.groups)
            behavior inEachGroupAny : (l: Line) -> Bool
            let inEachGroupAny (l) = List.all(g -> List.any(t -> t == "K", g.tags), l.groups)
            behavior comparedTrue : (l: Line) -> Int
            let comparedTrue (l) = if List.contains("K", l.tags) == true then 1 else 0
            behavior twoElements : (l: Line) -> Bool
            let twoElements (l) = List.contains("K", l.tags) && List.contains("L", l.tags)

            data Tagged = { tags: List<String> } invariant List.contains("K", tags)
            behavior heldBesideK : (t: Tagged) -> Bool
            let heldBesideK (t) = List.contains("L", t.tags)
            """;

    /** What a comparison of the elements draws is what holding the value in a list, a set or a
     *  map's keys draws, however the statement is written. */
    @Test
    void holdingTheValueDrawsTheLineComparingTheElementsWithItDraws() {
        assertEquals(Set.of("l.tags[*] K"), linesOf("any"));
        assertEquals(linesOf("any"), linesOf("listed"));
        assertEquals(linesOf("any"), linesOf("absent"));
        assertEquals(Set.of("l.ids[*] K"), linesOf("setted"));
        assertEquals(Set.of("l.rates[key] USD"), linesOf("keyed"));
        assertEquals(linesOf("keyed"), linesOf("guarded"));
        assertEquals(Set.of("l.nums[*] 5"), linesOf("numbered"));
        assertEquals(Set.of("l.days[*] 2026-01-05"), linesOf("anyDay"));
        assertEquals(linesOf("anyDay"), linesOf("hasDay"));
    }

    /** A container the source wrote out, asked for a value of the input, draws the lines the
     *  comparison of its elements with that value draws, and a row is found at the same points. */
    @Test
    void aWrittenContainerDrawsTheLinesOfTheComparison() {
        assertEquals(Set.of("l.s A", "l.s B"), linesOf("ofWrittenListAny"));
        assertEquals(linesOf("ofWrittenListAny"), linesOf("ofWrittenList"));
        assertEquals(linesOf("ofWrittenListAny"), linesOf("ofWrittenSet"));
        assertEquals(linesOf("ofWrittenIntsAny"), linesOf("ofWrittenInts"));
        assertEquals(pointsOf("ofWrittenListAny"), pointsOf("ofWrittenList"));
        assertEquals(pointsOf("ofWrittenIntsAny"), pointsOf("ofWrittenInts"));
    }

    /** Written beside other statements, under a closure or twice over one container, the lines
     *  are those the comparison written with {@code any} draws, each with its rows. */
    @Test
    void theLinesAreTheSameWhereTheStatementIsPartOfAnother() {
        for (String[] pair : new String[][] {
            { "alongside", "alongsideAny" }, { "either", "eitherAny" },
            { "inEachGroup", "inEachGroupAny" }, { "combined", "combinedAny" },
            { "nestedFirst", "nestedFirstAny" }, { "nested", "nestedAny" }, { "exactlyOne", "exactlyOneAny" },
            { "hasTime", "anyTime" }, { "hasInstant", "anyInstant" }, { "hasAt", "anyAt" },
            { "hasEmoji", "anyEmoji" }, { "hasDay", "anyDay" } }) {
            assertEquals(pointsOf(pair[1]), pointsOf(pair[0]), pair[0]);
        }
        assertEquals(Set.of("l.n 3", "l.tags[*] K"), linesOf("combined"));
        // The line of an application a comparison with an element of the closure precedes is the
        // line it is where nothing does, whichever way round the two sides of it are written.
        assertEquals(rowsFound("nestedDAny"), rowsFound("nestedD"));
        assertEquals(9, rowsFound("nestedD"));
        assertEquals(Set.of("l.n 3", "l.tags[*] K"), linesOf("alongside"));
        assertEquals(Set.of("l.tags[*] K", "l.other[*] M"), linesOf("either"));
        assertEquals(Set.of("l.groups[*].tags[*] K"), linesOf("inEachGroup"));
        assertEquals(Set.of("l.tags[*] K", "l.tags[*] L"), linesOf("twoElements"));
    }

    /** Every point of every line is searched, and the row found holds what the point says of the
     *  elements: the value at the line, an element below it or above it beside it. */
    @Test
    void everyPointHasARowThatHoldsWhatItSaysOfTheElements() {
        pointsHold("listed", "tags", Kind.TEXT, "K");
        pointsHold("setted", "ids", Kind.TEXT, "K");
        pointsHold("keyed", "rates", Kind.KEY, "USD");
        pointsHold("absent", "tags", Kind.TEXT, "K");
        pointsHold("guarded", "rates", Kind.KEY, "USD");
        pointsHold("numbered", "nums", Kind.NUMBER, "5");
        pointsHold("hasDay", "days", Kind.DAY, "2026-01-05");
    }

    /** The two sides of the line are owed where the neighbour of the value exists: a number and
     *  a date have one a step either side, a string has none. */
    @Test
    void aNumberAndADateHaveTheirNeighboursAndAStringHasNone() {
        assertEquals(Set.of("AtTheLine", "BesideTheLine[side=BELOW]",
                "BesideTheLine[side=ABOVE]", "InTheRegion[side=BELOW]",
                "InTheRegion[side=ABOVE]"), certifiedPointsOf("numbered"));
        assertEquals(certifiedPointsOf("numbered"), certifiedPointsOf("hasDay"));
        assertEquals(Set.of("AtTheLine", "InTheRegion[side=BELOW]", "InTheRegion[side=ABOVE]"),
                certifiedPointsOf("listed"));
    }

    /** A container that must hold another value is still asked for the one the line is at: a
     *  row at it holds both, and a row beside it holds one below or above and the one it must. */
    @Test
    void aContainerThatMustHoldAnotherValueIsStillAskedForTheLine() {
        assertEquals(Set.of("t.tags[*] L"), linesOf("heldBesideK"));
        pointsHold("heldBesideK", "tags", Kind.TEXT, "L");
        for (BorderAssessment border : borders("heldBesideK")) {
            for (ItemAssessment item : border.items().values()) {
                String row = certified(item);
                if (row != null) {
                    assertTrue(elements(row, "tags", Kind.TEXT).contains("K"), row);
                }
            }
        }
    }

    /** The statement is one reading and not two: a comparison of it with {@code true} does not
     *  also say it relates the value to another value. */
    @Test
    void theReportDoesNotSayItRelatesTheValueToAnotherWhereItDrawsALine() {
        String report = AdequacyReport.of(measured()).humanInEnglish(
                SourceRendering.namedByIdentity(SourceLayouts.NONE));
        for (String line : report.split("\n")) {
            assertFalse(line.contains("relates the value here to another value")
                    && line.contains("l.tags[*]"), line);
        }
        assertEquals(linesOf("comparedTrue"), Set.of("l.tags[*] K"));
    }

    /** A closure applied to each element of a written list states, on each application, what it is
     *  handed there: one line for each of the values the list writes, as {@code any} draws. */
    @Test
    void anApplicationInAClosureStatesWhatEachApplicationIsHanded() {
        assertEquals(Set.of("l.tags[*] K", "l.tags[*] L"), linesOf("mappedAny"));
        assertEquals(linesOf("mappedAny"), linesOf("mapped"));
    }

    /** A line one application of a closure draws is met through that application: a row at it is
     *  found where the other applications are made on other elements, as it is where one is. */
    @Test
    void aLineOneApplicationDrawsIsMetThroughThatApplication() {
        assertEquals(6, rowsFound("mappedAny"));
        assertEquals(pointsOf("mappedAny"), pointsOf("mapped"));
    }

    /** An application that states nothing on some application of the closure — a member asked of
     *  no element — leaves the lines of the others drawn, with the points the comparison has. */
    @Test
    void anApplicationThatStatesNothingDoesNotStopTheOthers() {
        assertEquals(Set.of("l.s K"), linesOf("mixedAny"));
        assertEquals(pointsOf("mixedAny"), pointsOf("mixed"));
    }

    /** Applications within the figure that draw more lines on one quantity than the figure allows
     *  between them draw none: one application draws two, and the figure counts lines. */
    @Test
    void applicationsDrawingMoreLinesThanTheFigureAllowsBetweenThemDrawNone() {
        int applications = CompositionBudget.READINGS_OF_ONE_CONDITION.maximum();
        String written = IntStream.range(0, applications).mapToObj(i -> "\"v" + i + "\"")
                .collect(Collectors.joining(", "));
        String source = """
                module probe
                data Line = { s: String }
                behavior mapped : (l: Line) -> List<Bool>
                let mapped (l) = List.map(k -> List.contains(l.s, [k, "Z"]), [%s])
                """.formatted(written);
        assertEquals(List.of(), Adequacy.readingsOf(measured(source).db(), "probe")
                .getOrDefault("mapped", List.of()));
    }

    /** The keys and the values of a map are asked for a member as the map is: the same line at the
     *  same points, with the same rows. */
    @Test
    void theKeysAndTheValuesOfAMapAreAskedAsTheMapIs() {
        assertEquals(pointsOf("keyed"), pointsOf("listedKeys"));
        assertEquals(Set.of("l.rates[*] 5"), linesOf("listedValues"));
        assertEquals(certifiedPointsOf("numbered"), certifiedPointsOf("listedValues"));
    }

    /** A map is composed holding the entry a line asks for beside the size the way asks of it, so
     *  a comparison with the keys or the values of a map has its rows as one with a list's. */
    @Test
    void aMapHoldsTheEntryALineAsksForBesideTheSizeTheWayAsksOfIt() {
        assertEquals(pointsOf("keyed"), pointsOf("anyKey"));
        assertEquals(certifiedPointsOf("numbered"), certifiedPointsOf("anyValue"));
        assertEquals(certifiedPointsOf("hasDay"), certifiedPointsOf("anyDatedKey"));
    }

    /** A map keyed by a date or a time is handed to a row as the text its keys cross as, so the
     *  rows at the points of the line are found as they are for a list of dates or of times. */
    @Test
    void aMapKeyedByATemporalHasRowsAtTheLineOfItsKey() {
        assertEquals(Set.of("l.dated[key] 2026-01-05"), linesOf("datedKey"));
        assertEquals(certifiedPointsOf("hasDay"), certifiedPointsOf("datedKey"));
        assertEquals(certifiedPointsOf("hasTime"), certifiedPointsOf("timedKey"));
    }

    /** The member being another place of the row relates two values and divides neither. */
    @Test
    void aMemberThatIsAnotherPlaceDrawsNoLine() {
        assertEquals(Set.of(), linesOf("another"));
        assertEquals(Set.of(), linesOf("anotherListed"));
        assertEquals(Set.of(), linesOf("anotherFiltered"));
        assertEquals(Set.of(), linesOf("anotherTaken"));
    }

    /** A container built out of another by an operation holds elements of the other, so the value
     *  asked of it is a line on them, as the comparison of those elements with it is. */
    @Test
    void aContainerBuiltOutOfAnotherDrawsTheLinesOfTheComparisonOfItsElements() {
        for (String[] pair : new String[][] {
            { "filteredNums", "filteredNumsAny" }, { "filteredKeys", "filteredKeysAny" },
            { "taken", "takenAny" }, { "dropped", "droppedAny" },
            { "distinctTags", "distinctTagsAny" }, { "removedKeys", "removedKeysAny" },
            { "chained", "chainedAny" }, { "mappedMember", "mappedMemberAny" },
            { "keysOfKept", "keysOfKeptAny" }, { "valuesOfKept", "valuesOfKeptAny" },
            { "keysOfTaken", "keysOfTakenAny" }, { "valuesOfTaken", "valuesOfTakenAny" },
            { "valuesOfIntersected", "valuesOfIntersectedAny" },
            { "keysOfRewritten", "keysOfRewrittenAny" },
            { "valuesOfRewritten", "valuesOfRewrittenAny" },
            { "removedItself", "removedItselfAny" }, { "emptiedSet", "emptiedSetAny" },
            { "emptiedMap", "emptiedMapAny" },
            { "keptOfDistinct", "keptOfDistinctAny" }, { "distinctOfKept", "distinctOfKeptAny" },
            { "sortOfTaken", "sortOfTakenAny" }, { "takenOfSorted", "takenOfSortedAny" },
            { "keptByRemainder", "keptByRemainderAny" },
            { "alongsideTaken", "alongsideTakenAny" }, { "eitherTaken", "eitherTakenAny" },
            { "mappedTaken", "mappedTakenAny" } }) {
            assertEquals(linesOf(pair[1]), linesOf(pair[0]), pair[0]);
        }
        assertEquals(Set.of("l.ids[*] K"), linesOf("removedFromSet"));
        // A key an answer holds is one its map held, so a map made of another by operations that
        // hold some of its keys is listed at the keys of the other; a value of one that rewrote
        // the values is no value of the other.
        assertEquals(Set.of("l.rates[*] 3", "l.rates[key] K"), linesOf("keysOfKept"));
        assertEquals(Set.of("l.rates[*] 3", "l.rates[*] 5"), linesOf("valuesOfKept"));
        assertEquals(Set.of("l.rates[key] K"), linesOf("keysOfTaken"));
        assertEquals(Set.of("l.rates[*] 5"), linesOf("valuesOfTaken"));
        assertEquals(Set.of("l.rates[key] K"), linesOf("keysOfRewritten"));
        assertEquals(Set.of(), linesOf("valuesOfRewritten"));
        // The line the filter draws is kept beside the one the value draws, whichever of the two
        // operations is outside.
        assertEquals(Set.of("l.nums[*] 3", "l.nums[*] 5"), linesOf("keptOfDistinct"));
        assertEquals(Set.of("l.nums[*] 3", "l.nums[*] 5"), linesOf("distinctOfKept"));
        // What the operations above a window kept is held beside what is asked of the element: the
        // window leaves which elements meet a statement as it was, so the points of the lines, and
        // which of them anyone is owed, are those of the same membership without it. Where the
        // value is one the kept statement refuses, the points say so too.
        assertEquals(owedPointsOf("filteredNums"), owedPointsOf("keptOfDistinct"));
        assertEquals(owedPointsOf("filteredNums"), owedPointsOf("distinctOfKept"));
        assertEquals(owedPointsOf("keptAgainstTheValueWithoutIt"),
                owedPointsOf("keptAgainstTheValue"));
        assertEquals(linesOf("keptAgainstTheValueWithoutIt"), linesOf("keptAgainstTheValue"));
        assertEquals(Set.of("l.nums[*] 3", "l.nums[*] 5"), linesOf("filteredNums"));
        assertEquals(Set.of("l.rates[*] 3", "l.rates[key] USD"), linesOf("filteredKeys"));
        assertEquals(Set.of("l.tags[*] K"), linesOf("taken"));
        assertEquals(Set.of("l.rates[key] USD"), linesOf("removedKeys"));
    }

    private enum Kind { TEXT, KEY, NUMBER, DAY }

    /** Each certified row of {@code behavior}'s line holds, in {@code field}, what its point says
     *  against {@code at}. */
    private static void pointsHold(String behavior, String field, Kind kind, String at) {
        int checked = 0;
        for (BorderAssessment border : borders(behavior)) {
            for (Map.Entry<?, ItemAssessment> item : border.items().entrySet()) {
                String row = certified(item.getValue());
                if (row == null) {
                    continue;
                }
                String point = item.getKey().toString();
                List<String> held = elements(row, field, kind);
                boolean equal = held.stream().anyMatch(each -> compare(each, at, kind) == 0);
                boolean below = held.stream().anyMatch(each -> compare(each, at, kind) < 0);
                boolean above = held.stream().anyMatch(each -> compare(each, at, kind) > 0);
                if (point.startsWith("AtTheLine")) {
                    assertTrue(equal, behavior + " " + point + " " + row);
                } else if (point.endsWith("side=BELOW]")) {
                    assertTrue(below, behavior + " " + point + " " + row);
                } else {
                    assertTrue(above, behavior + " " + point + " " + row);
                }
                checked++;
            }
        }
        assertTrue(checked >= 3, behavior + " " + checked);
    }

    /** The order Souther puts the values of a position in, and not the order of the host's. */
    private static int compare(String element, String at, Kind kind) {
        return switch (kind) {
            case NUMBER -> Long.compare(Long.parseLong(element), Long.parseLong(at));
            case TEXT, KEY -> new Text(element).compareTo(new Text(at));
            case DAY -> element.compareTo(at);
        };
    }

    /** The elements {@code field} holds in {@code row}, as the text of each: the strings, the
     *  keys of a map, the numbers or the days. */
    private static List<String> elements(String row, String field, Kind kind) {
        Matcher held = Pattern.compile(field + " = \\[(.*?)\\](?:, \\w+ =| \\})").matcher(row);
        assertTrue(held.find(), row);
        String inside = held.group(1);
        Pattern each = switch (kind) {
            case TEXT -> Pattern.compile("\"([^\"]*)\"");
            case KEY -> Pattern.compile("\\(\"([^\"]*)\", ");
            case NUMBER -> Pattern.compile("(-?\\d+)");
            case DAY -> Pattern.compile("Date\\(\"([-0-9]+)\"\\)");
        };
        List<String> out = new ArrayList<>();
        Matcher found = each.matcher(inside);
        while (found.find()) {
            out.add(found.group(1));
        }
        return out;
    }

    private static Set<String> linesOf(String behavior) {
        Set<String> out = new TreeSet<>();
        borders(behavior).forEach(each -> out.add(each.left() + " " + each.value()));
        return out;
    }

    /**
     * Each point of each line of {@code behavior}, one by one: the line it is of, the point, whether
     * the rules say anyone is owed it, and whether a row was certified at it. Two statements that
     * mean one thing have one of these, and a point one of them is not owed or has no row for is
     * not hidden by a point of another line that has.
     */
    private static Set<String> pointsOf(String behavior) {
        Set<String> out = new TreeSet<>();
        for (BorderAssessment border : borders(behavior)) {
            for (Map.Entry<DomainPoint, ItemAssessment> item : border.items().entrySet()) {
                out.add(border.left() + " " + border.value() + " | "
                        + item.getKey().toString().replace("[]", "")
                        + " | owed=" + !border.border().about(item.getKey()).isEmpty()
                        + " | row=" + (certified(item.getValue()) != null));
            }
        }
        return out;
    }

    /** {@link #pointsOf}, without whether a row was found: a reading that asks no row of a
     *  container may still have one certified by what the search tried. */
    private static Set<String> owedPointsOf(String behavior) {
        return pointsOf(behavior).stream().map(each -> each.replaceAll(" \\| row=\\w+$", ""))
                .collect(Collectors.toCollection(TreeSet::new));
    }

    /** How many points of {@code behavior}'s lines a row was found for. */
    private static long rowsFound(String behavior) {
        return pointsOf(behavior).stream().filter(each -> each.endsWith("row=true")).count();
    }

    /** Which points of {@code behavior}'s lines a row was found for, by the name of the point. */
    private static Set<String> certifiedPointsOf(String behavior) {
        Set<String> out = new TreeSet<>();
        for (BorderAssessment border : borders(behavior)) {
            for (Map.Entry<?, ItemAssessment> item : border.items().entrySet()) {
                if (certified(item.getValue()) != null) {
                    out.add(item.getKey().toString().replace("[]", ""));
                }
            }
        }
        return out;
    }

    private static List<BorderAssessment> borders(String behavior) {
        List<BorderAssessment> lines = Adequacy.readingsOf(measured().db(), "probe").get(behavior);
        return lines == null ? List.of() : lines;
    }

    private static String certified(ItemAssessment item) {
        if (!(item instanceof ItemAssessment.Owed owed)) {
            return null;
        }
        for (ItemAssessment.Attempt attempt : owed.searches().each()) {
            if (attempt instanceof ItemAssessment.Attempt.Certified row) {
                return row.row().inputs().stream().map(each -> each.text()).toList().toString();
            }
        }
        return null;
    }

    @AfterAll
    static void released() {
        MEASURED.clear();
    }

    private static Compilation measured() {
        return measured(MODEL);
    }

    private static Compilation measured(String model) {
        return MEASURED.computeIfAbsent(model, source -> {
            Compilation compilation = Compilation.ofSource(source, "Main");
            compilation.measure(Adequacy.Asked.fullReport());
            compilation.answerEverything();
            assertEquals(List.of(), compilation.errors().stream()
                    .map(each -> each.diagnostic().code() + " " + each.diagnostic().said())
                    .toList(), source);
            return compilation;
        });
    }
}
