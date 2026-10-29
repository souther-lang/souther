package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.Located;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;
import souther.compiler.diag.Messages;
import souther.compiler.diag.Primary;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.OfferingRequest;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.Locale;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A fold owes a row in which its step reads what an earlier step answered, and a row of fewer than
 * two elements is not one.
 *
 * <p>A row of no element runs no step, and a row of one element runs the step once, on the seed. A
 * sum whose rows are those cannot be told from the fold stopping after its first element, nor from
 * every step being handed the seed in the place of what it carries: the seed is {@code 0}, which is
 * what {@code +} leaves alone. Both rewrites are asked of every fold a row enters, and a row of two
 * elements tells both apart.
 */
class AFoldOwesARowWhoseStepReadsWhatItCarriedTest {

    private static String total(String step, String rows) {
        return """
                module repro.total

                behavior total : (xs: List<Int>) -> Int

                let total (xs) = List.fold(%s, 0, xs)

                example total
                    | "nothing" : ([]) -> 0
                    | "one" : ([1]) -> 1
                %s""".formatted(step, rows);
    }

    private static final String SUM = total("(acc, x) -> acc + x", "");

    private static final String STOPS_AFTER_ONE_STEP =
            "! no row would come out differently if the fold (5:18) stopped after its first element";

    private static final String STEPS_FROM_THE_SEED =
            "! no row would come out differently if the fold (5:18) handed each step the seed in"
                    + " place of what the step before it answered";

    @Test
    void rowsOfFewerThanTwoElementsLeaveBothRewritesOfTheFoldAGap() {
        Compilation compilation = measured(SUM);

        assertEquals(List.of(STOPS_AFTER_ONE_STEP, STEPS_FROM_THE_SEED), rewriteLines(compilation));
        assertEquals(AdequacyReport.AdequacyStatus.NOT_SATISFIED,
                AdequacyReport.of(compilation).adequacy());
    }

    @Test
    void aRowOfTwoElementsTellsBothApart() {
        Compilation compilation =
                measured(total("(acc, x) -> acc + x", "    | \"two\" : ([3, 4]) -> 7\n"));

        assertEquals(List.of(), rewriteLines(compilation));
        assertEquals(AdequacyReport.AdequacyStatus.SATISFIED,
                AdequacyReport.of(compilation).adequacy());
    }

    /**
     * A step that never reads what it carries is the fold under another spelling once it is handed
     * the seed, and is not asked about that; stopping after one step is still another program, and
     * the two rows still cannot tell a fold keeping the last element from one keeping the first.
     */
    @Test
    void aStepThatNeverReadsWhatItCarriesIsAskedOnlyWhetherTheFoldGoesOn() {
        Compilation compilation = measured(total("(acc, x) -> x", ""));

        assertEquals(List.of(STOPS_AFTER_ONE_STEP), rewriteLines(compilation));
        // Not asked, rather than left open: the two values the rows came to and the one rewrite.
        assertTrue(page(compilation).lines().map(String::strip)
                        .anyMatch("replacement 2/3"::equals),
                () -> page(compilation));
    }

    /** A list written with one element is walked no further than its first, by either rewrite. */
    @Test
    void aListWrittenWithOneElementIsAWalkNeitherRewriteChanges() {
        Compilation compilation = measured("""
                module repro.one

                behavior plus : (n: Int) -> Int

                let plus (n) = List.fold((acc, x) -> acc + x, 0, [n])

                example plus
                    | "zero" : (0) -> 0
                    | "one" : (1) -> 1
                """);

        // The two values the rows came to, and nothing of the fold: not asked, rather than left
        // open for want of an input the search could not find.
        assertTrue(page(compilation).lines().map(String::strip)
                        .anyMatch("replacement 2/2"::equals),
                () -> page(compilation));
    }

    /** The row offered holds two elements, and is one row for both rewrites. */
    @Test
    void theRowOfferedHoldsTwoElementsAndIsOneRowForBoth() {
        Compilation compilation = measured(SUM);
        String block = GeneratedRows.of(Adequacy.offeredFor(compilation.db(),
                        OfferingRequest.overTheModule("repro.total")),
                Map.of(), SourceRendering.namedByIdentity(compilation.texts()),
                compilation.db()).text();

        List<RowsOfABlock.Row> rows = RowsOfABlock.of(block);
        assertEquals(1, rows.size(), () -> "one row: " + block);
        RowsOfABlock.Row row = rows.getFirst();
        assertTrue(row.isFor("the fold stopping after its first element")
                        && row.isFor("each step of the fold handed the seed"),
                () -> "for both rewrites: " + block);
        assertTrue(row.values().matches("\\(\\[-?\\d+, -?\\d+]\\) -> <\\?>"),
                () -> "a list of two elements: " + block);
    }

    /** A build is warned at the fold, and told which row to write. */
    @Test
    void aBuildIsWarnedAtTheFold() {
        Compilation compilation = warned(SUM);
        List<Located> warnings = rewriteWarnings(compilation);

        assertEquals(List.of(
                        "No row of `total` would come out differently if this fold stopped after"
                                + " its first element.",
                        "No row of `total` would come out differently if each step of this fold"
                                + " were handed the seed in place of what the step before it"
                                + " answered."),
                warnings.stream()
                        .map(each -> Messages.render(each.diagnostic().said(), Locale.ENGLISH))
                        .toList());
        for (Located each : warnings) {
            Primary.InSource at =
                    assertInstanceOf(Primary.InSource.class, each.diagnostic().primary());
            assertEquals(5, WhereItSits.in(SUM, at.place().region()).start().line(),
                    "the line of the fold");
            assertTrue(each.diagnostic().notes().stream()
                            .map(n -> Messages.render(n.said(), Locale.ENGLISH))
                            .anyMatch(n -> n.startsWith("Write a row at ([")),
                    () -> "and the row to write: " + each.diagnostic().notes());
        }
    }

    /**
     * A fold inside one of the language's own operations is one no row of fewer than two elements
     * tells apart either, and is said by the definition that wrote it, at the behavior: this build
     * holds no source of it to point at.
     */
    @Test
    void aFoldTheLanguageWritesIsSaidByTheDefinitionThatWroteIt() {
        Compilation compilation = warned("""
                module repro.mapped

                behavior doubled : (xs: List<Int>) -> List<Int>

                let doubled (xs) = List.map(x -> x * 2, xs)

                example doubled
                    | "nothing" : ([]) -> []
                    | "one" : ([1]) -> [2]
                """);

        assertEquals(List.of(
                        "No row of `doubled` would come out differently if a fold of"
                                + " `souther.list.map`, which this build holds no source of,"
                                + " stopped after its first element.",
                        "No row of `doubled` would come out differently if each step of a fold of"
                                + " `souther.list.map`, which this build holds no source of, were"
                                + " handed the seed in place of what the step before it answered."),
                rewriteWarnings(compilation).stream()
                        .map(each -> Messages.render(each.diagnostic().said(), Locale.ENGLISH))
                        .toList());
    }

    /** The rewrites asked of the fold, with where it stands left out. */
    private static List<String> rewritesAsked(Compilation compilation) {
        return rewriteLines(compilation).stream()
                .map(line -> line.replaceAll("\\(\\d+:\\d+\\)", "(here)")).toList();
    }

    private static final List<String> BOTH_ASKED = List.of(
            "! no row would come out differently if the fold (here) stopped after its first element",
            "! no row would come out differently if the fold (here) handed each step the seed in"
                    + " place of what the step before it answered");

    /** A step spelled as a name is the step all the same: the fold is walked, and asked. */
    @Test
    void aStepBoundToANameIsAskedLikeOneWrittenWhereItIsHanded() {
        assertEquals(BOTH_ASKED, rewritesAsked(measured("""
                module repro.local

                behavior total : (xs: List<Int>) -> Int

                let total (xs) = {
                    let step = (acc, x) -> acc + x
                    List.fold(step, 0, xs)
                }

                example total
                    | "nothing" : ([]) -> 0
                    | "one" : ([1]) -> 1
                """)));
        assertEquals(BOTH_ASKED, rewritesAsked(measured("""
                module repro.declared

                behavior total : (xs: List<Int>) -> Int

                let step (acc: Int, x: Int): Int = acc + x

                let total (xs) = List.fold(step, 0, xs)

                example total
                    | "nothing" : ([]) -> 0
                    | "one" : ([1]) -> 1
                """)));
        assertEquals(BOTH_ASKED, rewritesAsked(measured("""
                module repro.handed

                behavior total : (xs: List<Int>) -> Int

                let summed (step: (Int, Int) -> Int, ys: List<Int>): Int = List.fold(step, 0, ys)

                let total (xs) = summed((acc, x) -> acc + x, xs)

                example total
                    | "nothing" : ([]) -> 0
                    | "one" : ([1]) -> 1
                """)));
    }

    private static String overASet(String listed) {
        return """
                module repro.unordered

                behavior total : (s: Set<Int>) -> Int

                let total (s) = List.fold((acc, x) -> acc + x, 0, %s)

                example total
                    | "nothing" : (Set.fromList([])) -> 0
                    | "one" : (Set.fromList([1])) -> 1
                """.formatted(listed);
    }

    /**
     * A list made of what a set lists has the order the host happened to keep, and the model names
     * no first element in it: the walk is not asked, however the list was worked on after it was
     * made. Ordering it gives it an order, and the walk is asked again.
     */
    @Test
    void aListMadeOfWhatASetListsIsWalkedInNoOrderTheModelNames() {
        for (String listed : List.of("Set.toList(s)", "List.reverse(Set.toList(s))",
                "List.map(x -> x, Set.toList(s))", "List.take(1, List.reverse(Set.toList(s)))")) {
            assertEquals(List.of(), rewritesAsked(measured(overASet(listed))), listed);
        }
        assertEquals(List.of(), rewritesAsked(measured("""
                module repro.helped

                behavior total : (s: Set<Int>) -> Int

                let items (t: Set<Int>): List<Int> = Set.toList(t)

                let total (s) = List.fold((acc, x) -> acc + x, 0, items(s))

                example total
                    | "nothing" : (Set.fromList([])) -> 0
                    | "one" : (Set.fromList([1])) -> 1
                """)), "a helper that lists it is the list it lists");
        assertEquals(BOTH_ASKED.size(), rewritesAsked(measured(overASet(
                "List.sort(Set.toList(s))"))).size(), "sorted, it has an order again");
        assertEquals(BOTH_ASKED.size(), rewritesAsked(measured(overASet(
                "List.reverse(List.sort(Set.toList(s)))"))).size());
    }

    /** What a map lists is as unordered as what a set lists. */
    @Test
    void aListMadeOfWhatAMapListsIsWalkedInNoOrderTheModelNames() {
        for (String listed : List.of("Map.values(m)", "List.reverse(Map.values(m))")) {
            assertEquals(List.of(), rewritesAsked(measured("""
                    module repro.mapped

                    behavior total : (m: Map<String, Int>) -> Int

                    let total (m) = List.fold((acc, x) -> acc + x, 0, %s)

                    example total
                        | "nothing" : (Map.empty) -> 0
                        | "one" : (Map.fromList([("a", 1)])) -> 1
                    """.formatted(listed))), listed);
        }
        assertEquals(List.of(), rewritesAsked(measured("""
                module repro.keyed

                behavior total : (m: Map<String, Int>) -> Int

                let total (m) = List.fold((acc, k) -> acc + String.length(k), 0, Map.keys(m))

                example total
                    | "nothing" : (Map.empty) -> 0
                    | "one" : (Map.fromList([("a", 1)])) -> 1
                """)));
    }

    /** A list held in a field of a record is a list the rows tell the rewrites apart on all the same. */
    @Test
    void aListInAFieldOfARecordIsGivenARowOfTwoElements() {
        Compilation compilation = measured("""
                module repro.held

                data Input = { xs: List<Int> }

                behavior total : (input: Input) -> Int

                let total (input) = List.fold((acc, x) -> acc + (1 - acc) * x, 0, input.xs)

                example total
                    | "nothing" : (Input { xs = [] }) -> 0
                    | "one" : (Input { xs = [1] }) -> 1
                """);
        String block = GeneratedRows.of(Adequacy.offeredFor(compilation.db(),
                        OfferingRequest.overTheModule("repro.held")),
                Map.of(), SourceRendering.namedByIdentity(compilation.texts()),
                compilation.db()).text();

        List<RowsOfABlock.Row> rows = RowsOfABlock.of(block);
        // Stopping after one step parts from the fold where the second element is read before the
        // first has lifted the accumulator, and the seed where it is read after: one row each.
        assertEquals(2, rows.size(), () -> block);
        assertTrue(rows.stream().anyMatch(row -> row.isFor("the fold stopping after its first element")
                        && row.values().contains("xs = [0, 1]")), () -> block);
        assertTrue(rows.stream().anyMatch(row -> row.isFor("each step of the fold handed the seed")
                        && row.values().contains("xs = [1, 0]")), () -> block);
    }

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String STEPS = """
            let add (acc: Int, x: Int): Int = acc + x
            let sub (acc: Int, x: Int): Int = acc - x
            """;

    /** What each rewrite of a fold came to, as the document says: the rewrite, how it stands and
     *  why it is open. */
    private static List<String> foldVerdicts(Compilation compilation) {
        List<String> out = new ArrayList<>();
        JsonNode replacement = JSON.readTree(AdequacyReport.of(compilation)
                        .json(SourceRendering.namedByIdentity(compilation.texts())))
                .get("modules").get(0).get("behaviors").get(0).get("replacement");
        for (JsonNode each : replacement.get("obligations")) {
            String rewrite = each.get("obligationId").get("rewrite").asString();
            if (!rewrite.startsWith("fold_")) {
                continue;
            }
            List<String> because = new ArrayList<>();
            if (each.has("undecidedBecause")) {
                each.get("undecidedBecause").forEach(word -> because.add(word.asString()));
            }
            out.add(rewrite + ": " + each.get("disposition").asString()
                    + (because.isEmpty() ? "" : " because " + String.join(", ", because)));
        }
        return out;
    }

    private static final List<String> LEFT_OPEN = List.of(
            "fold_after_one_step: undecided because step_not_expanded",
            "fold_from_the_seed: undecided because step_not_expanded");

    /**
     * A step chosen as the program runs is a fold the language owes rows of all the same. This
     * build cannot run it rewritten, and says so: the adequacy is undetermined, and not satisfied
     * by rows that were never put to the fold.
     */
    @Test
    void aStepChosenAsTheProgramRunsLeavesTheFoldOpen() {
        Compilation compilation = measured("""
                module repro.chosen

                data In = { flag: Bool, xs: List<Int> }

                behavior total : (i: In) -> Int

                %s
                let total (i) = {
                    let step = if i.flag then add else sub
                    List.fold(step, 0, i.xs)
                }

                example total
                    | "t0" : (In { flag = true, xs = [] }) -> 0
                    | "t1" : (In { flag = true, xs = [1] }) -> 1
                    | "f0" : (In { flag = false, xs = [] }) -> 0
                    | "f1" : (In { flag = false, xs = [1] }) -> -1
                """.formatted(STEPS));

        assertEquals(LEFT_OPEN, foldVerdicts(compilation));
        assertEquals(AdequacyReport.AdequacyStatus.UNDETERMINED,
                AdequacyReport.of(compilation).adequacy());
        assertEquals(List.of(), rewriteLines(compilation), "no gap is claimed of a fold not run");
    }

    /** The fold that can be run rewritten is asked as ever, beside the one that cannot. */
    @Test
    void aFoldWhoseStepIsWrittenWhereItIsHandedIsAskedBesideOneThatIsNot() {
        Compilation compilation = measured("""
                module repro.mixed

                data In = { flag: Bool, xs: List<Int> }

                behavior total : (i: In) -> Int

                %s
                let total (i) = {
                    let step = if i.flag then add else sub
                    List.fold(step, 0, i.xs) + List.fold((acc, x) -> acc + x, 0, i.xs)
                }

                example total
                    | "t0" : (In { flag = true, xs = [] }) -> 0
                    | "t1" : (In { flag = true, xs = [1] }) -> 2
                    | "f0" : (In { flag = false, xs = [] }) -> 0
                    | "f1" : (In { flag = false, xs = [1] }) -> 0
                """.formatted(STEPS));

        assertEquals(List.of(
                        "fold_after_one_step: unnoticed", "fold_from_the_seed: unnoticed",
                        "fold_after_one_step: undecided because step_not_expanded",
                        "fold_from_the_seed: undecided because step_not_expanded"),
                foldVerdicts(compilation).stream()
                        .sorted(Comparator.comparing((String v) -> v.contains("undecided")))
                        .toList());
        assertEquals(2, rewriteLines(compilation).size(), "the written fold is asked");
    }

    /**
     * A list written with one element is walked no further than its first, whatever the step and
     * however the list reaches the fold: written there, bound to a name, or put in another order.
     */
    @Test
    void aListOfOneElementIsNotAskedWhateverTheStepIs() {
        for (String walked : List.of("[i.n]", "ys", "List.reverse(ys)", "List.sort([i.n])")) {
            Compilation compilation = measured("""
                    module repro.single

                    data In = { flag: Bool, n: Int }

                    behavior total : (i: In) -> Int

                    %s
                    let total (i) = {
                        let ys = [i.n]
                        let step = if i.flag then add else sub
                        List.fold(step, 0, %s)
                    }

                    example total
                        | "t" : (In { flag = true, n = 1 }) -> 1
                        | "f" : (In { flag = false, n = 1 }) -> -1
                    """.formatted(STEPS, walked));

            assertEquals(List.of(), foldVerdicts(compilation), walked);
        }
    }

    private static final String THROWS = """
            module repro.nested

            data Throw = List<Int>

            behavior score : (throws: List<Throw>) -> Int

            let score (throws) = List.fold((acc, t) -> acc + List.length(t.value), 0, throws)

            example score
                | ([]) -> 0
                | ([Throw([])]) -> 0
                | ([Throw([12])]) -> 1
                | ([Throw([1, 2])]) -> 2
                | ([Throw([1, 2, 3])]) -> 3
            %s""";

    /**
     * A candidate whose walked list holds fewer than two elements is not run under the rewrite,
     * so the runs of the search are spent on lists of two, and a row whose answer is right added
     * to the rows does not leave the rewrites undecided.
     */
    @Test
    void aRowWhoseAnswerIsRightDoesNotLeaveTheFoldUndecidedForLackOfRuns() {
        StringBuilder many = new StringBuilder();
        for (int k = 1; k <= 14; k++) {
            many.append("    | ([Throw([%d, %d])]) -> 2\n".formatted(k, k + 20));
        }
        for (String more : List.of("", "    | ([Throw([5, 8])]) -> 2\n",
                "    | ([Throw([5, 8])]) -> 2\n    | ([Throw([4, 6, 9, 7])]) -> 4\n"
                        + "    | ([Throw([3, 3, 3, 3, 3])]) -> 5\n    | ([Throw([2, 1, 0])]) -> 3\n",
                many.toString())) {
            Compilation compilation = measured(THROWS.formatted(more));

            assertEquals(List.of("fold_after_one_step: unnoticed", "fold_from_the_seed: unnoticed"),
                    foldVerdicts(compilation), more);
        }
    }

    private static final String GUARDED_TO_ONE = """
            module repro.pins

            data Pin = Int
                invariant value >= 1 && value <= 12

            data Throw = List<Pin>
                invariant List.allDistinctBy(p -> p, value)

            behavior points : (t: Throw) -> Int

            let points (t) = {
                let n = List.length(t.value)
                if n == 1 then List.sum(List.map(p -> p.value, t.value)) else n
            }

            example points
                | (Throw([])) -> 0
                | (Throw([Pin(12)])) -> 12
                | (Throw([Pin(1), Pin(2)])) -> 2
                | (Throw([Pin(1), Pin(2), Pin(3)])) -> 3
            """;

    /**
     * A walk inside an arm that holds only where its list has one element at most has nothing a
     * row could tell a rewrite of it by: no search is run, and no gap is claimed or left open.
     */
    @Test
    void aWalkInAnArmThatHoldsOnlyForAListOfOneElementAtMostOwesNothing() {
        Compilation compilation = measured(GUARDED_TO_ONE);

        assertEquals(List.of(), foldVerdicts(compilation));
        assertEquals(AdequacyReport.AdequacyStatus.SATISFIED,
                AdequacyReport.of(compilation).adequacy());
    }

    private static String foldOverWhatAnInvariantHolds(String bound, String rows) {
        return """
                module repro.few

                data Few = List<Int>
                    invariant atMost = List.length(value) <= %s

                behavior total : (xs: Few) -> Int

                let total (xs) = List.fold((acc, x) -> acc + x, 0, xs.value)

                example total
                %s""".formatted(bound, rows);
    }

    /** The rules of the input's own declarations hold the list to one element at most, with no
     *  condition in the body saying so: there is nothing for a row to tell a rewrite by. */
    @Test
    void aWalkOverAListTheDeclarationsHoldToOneElementAtMostOwesNothing() {
        Compilation compilation = measured(foldOverWhatAnInvariantHolds("1", """
                    | (Few([])) -> 0
                    | (Few([5])) -> 5
                """));

        assertEquals(List.of(), foldVerdicts(compilation));
        assertEquals(AdequacyReport.AdequacyStatus.SATISFIED,
                AdequacyReport.of(compilation).adequacy());
    }

    /** Room for a second element is room for a row that tells the rewrites apart. */
    @Test
    void aWalkOverAListTheDeclarationsLeaveRoomForTwoElementsIsStillAsked() {
        Compilation compilation = measured(foldOverWhatAnInvariantHolds("2", """
                    | (Few([])) -> 0
                    | (Few([5])) -> 5
                """));

        assertEquals(2, foldVerdicts(compilation).size());
    }

    private static final String FOLD_OF_XS = "List.fold((acc, x) -> acc + x, 0, i.xs)";

    /** A second element is looked for and not found, or the list is dropped past its first and
     *  nothing is left: either way the walk is entered with one element at most. */
    @Test
    void aWalkWhereTheSecondElementIsAbsentOwesNothing() {
        String body = "match List.get(1, i.xs) with\n | Some s -> 0\n | None -> " + FOLD_OF_XS;

        assertEquals(List.of(), verdictsOfTheFoldIn(body, ONE_OR_NONE_ANSWER_ROWS));
    }

    /**
     * {@code List.drop} is a fold of the library's, which is asked about like any other: its two
     * rewrites are what is left once the model's own fold is shown to owe nothing.
     */
    @Test
    void aWalkWhereNothingIsLeftAfterTheFirstElementOwesNothing() {
        String body = "if List.isEmpty(List.drop(1, i.xs)) then " + FOLD_OF_XS + " else 0";

        assertEquals(List.of("fold_after_one_step: noticed", "fold_from_the_seed: noticed"),
                verdictsOfTheFoldIn(body, ONE_OR_NONE_ANSWER_ROWS));
    }

    /** One fold written once but entered from two places is owed where any of them is not shown. */
    @Test
    void aWalkShownToHoldOneElementAtMostAtOnePlaceOnlyIsStillAsked() {
        Compilation compilation = measured("""
                module repro.twice

                data In = { xs: List<Int>, ys: List<Int> }

                behavior total : (i: In) -> Int

                let sum (zs: List<Int>) = List.fold((acc, x) -> acc + x, 0, zs)

                let total (i) =
                    if List.length(i.xs) <= 1 then sum(i.xs) + sum(i.ys) else 0

                example total
                    | (In { xs = [], ys = [] }) -> 0
                    | (In { xs = [5], ys = [] }) -> 5
                    | (In { xs = [5], ys = [1, 2] }) -> 8
                """);

        assertEquals(2, foldVerdicts(compilation).size());
    }

    /** The same shapes with the walk on the other side of the condition leave room for two. */
    @Test
    void aWalkWhereTheSecondElementIsPresentIsStillAsked() {
        Map<String, Integer> bodies = new java.util.LinkedHashMap<>();
        bodies.put("match List.get(1, i.xs) with\n | Some s -> " + FOLD_OF_XS + "\n | None -> 0",
                2);
        bodies.put("if List.isEmpty(List.drop(1, i.xs)) then 0 else " + FOLD_OF_XS, 4);

        bodies.forEach((body, count) -> assertEquals(count,
                verdictsOfTheFoldIn(body, ROOM_FOR_TWO_ROWS.formatted(0, 3)).size(), body));
    }
    private static List<String> verdictsOfTheFoldIn(String body, String rows) {
        return foldVerdicts(measured("""
                module repro.guarded

                data In = { xs: List<Int>, ys: List<Int> }

                behavior total : (i: In) -> Int

                let total (i) = %s

                example total
                %s""".formatted(body, rows)));
    }

    private static final String ONE_OR_NONE_ANSWER_ROWS = """
                | (In { xs = [], ys = [] }) -> 0
                | (In { xs = [5], ys = [] }) -> 5
                | (In { xs = [1, 2], ys = [] }) -> 0
            """;

    /** Every way a condition the arm is inside says the length is one at most, and only those. */
    @Test
    void aConditionOfTheWalkedListsLengthSaysItIsOneAtMostOnlyWhereItDoes() {
        for (String body : List.of(
                "if List.length(i.xs) == 1 then " + FOLD_OF_XS + " else 0",
                "if List.length(i.xs) <= 1 then " + FOLD_OF_XS + " else 0",
                "if List.length(i.xs) < 2 then " + FOLD_OF_XS + " else 0",
                "if 1 == List.length(i.xs) then " + FOLD_OF_XS + " else 0",
                "if 2 > List.length(i.xs) then " + FOLD_OF_XS + " else 0",
                "if List.length(i.xs) > 1 then 0 else " + FOLD_OF_XS,
                "if List.length(i.xs) >= 2 then 0 else " + FOLD_OF_XS,
                "if List.length(i.xs) == 1 && List.length(i.ys) == 0 then " + FOLD_OF_XS
                        + " else 0",
                "{ let n = List.length(i.xs)\n if n == 1 then " + FOLD_OF_XS + " else 0 }")) {
            assertEquals(List.of(), verdictsOfTheFoldIn(body, ONE_OR_NONE_ANSWER_ROWS), body);
        }
    }

    private static final String ROOM_FOR_TWO_ROWS = """
                | (In { xs = [], ys = [] }) -> 0
                | (In { xs = [5], ys = [] }) -> %d
                | (In { xs = [1, 2], ys = [] }) -> %d
            """;

    /** A condition that leaves room for two elements, or is of another list, says nothing: the
     *  rewrites are still asked of the walk. */
    @Test
    void aConditionThatLeavesRoomForTwoElementsOrIsOfAnotherListSaysNothing() {
        Map<String, String> bodies = new java.util.LinkedHashMap<>();
        bodies.put("if List.length(i.xs) == 2 then " + FOLD_OF_XS + " else 0",
                ROOM_FOR_TWO_ROWS.formatted(0, 3));
        bodies.put("if List.length(i.xs) >= 1 then " + FOLD_OF_XS + " else 0",
                ROOM_FOR_TWO_ROWS.formatted(5, 3));
        bodies.put("if List.length(i.xs) <= 2 then " + FOLD_OF_XS + " else 0",
                ROOM_FOR_TWO_ROWS.formatted(5, 3));
        bodies.put("if List.length(i.xs) == 1 then 0 else " + FOLD_OF_XS,
                ROOM_FOR_TWO_ROWS.formatted(0, 3));
        bodies.put("if List.length(i.ys) <= 1 then " + FOLD_OF_XS + " else 0",
                ROOM_FOR_TWO_ROWS.formatted(5, 3));
        bodies.put("if List.length(i.xs) == 1 || List.length(i.ys) == 1 then " + FOLD_OF_XS
                + " else 0", ROOM_FOR_TWO_ROWS.formatted(5, 0));

        bodies.forEach((body, rows) ->
                assertEquals(2, verdictsOfTheFoldIn(body, rows).size(), body));
    }

    /** The list a walk goes over is found through the newtype wearing it as it is without. */
    @Test
    void aListWornByANewtypeIsGrownAsOneNotWornIs() {
        StringBuilder many = new StringBuilder();
        for (int k = 1; k <= 14; k++) {
            many.append("    | (Throws([Throw([%d, %d])])) -> 2\n".formatted(k, k + 20));
        }
        Compilation compilation = measured("""
                module repro.worn

                data Throw = List<Int>
                data Throws = List<Throw>

                behavior score : (throws: Throws) -> Int

                let score (throws) =
                    List.fold((acc, t) -> acc + List.length(t.value), 0, throws.value)

                example score
                    | (Throws([])) -> 0
                    | (Throws([Throw([])])) -> 0
                    | (Throws([Throw([12])])) -> 1
                %s""".formatted(many));

        assertEquals(List.of("fold_after_one_step: unnoticed", "fold_from_the_seed: unnoticed"),
                foldVerdicts(compilation));
    }

    /**
     * A run through a fold it cannot see the end of records no second element, and that is not a
     * list of one: a list fixed in the model that holds two is left open all the same.
     */
    @Test
    void aFixedListIsNotShownToHoldOneElementByAFoldNoRunSawTheEndOf() {
        Compilation compilation = measured("""
                module repro.fixed

                behavior total : (flag: Bool) -> Int

                %s
                let total (flag) = {
                    let step = if flag then add else sub
                    List.fold(step, 0, [1, 2])
                }

                example total
                    | "t" : (true) -> 3
                    | "f" : (false) -> -3
                """.formatted(STEPS));

        assertEquals(LEFT_OPEN, foldVerdicts(compilation));
    }

    /**
     * A fold written once in a helper is one walk however many places the helper is called from,
     * and one place that cannot run it rewritten leaves it open at all of them: a rewrite of it is
     * an edit of the one source.
     */
    @Test
    void aHelpersFoldIsOpenAtEveryCallWhenOneCallHandsItAStepItCannotRun() {
        Compilation compilation = measured("""
                module repro.shared

                data In = { flag: Bool, xs: List<Int> }

                behavior total : (i: In) -> Int

                %s
                let summed (step: (Int, Int) -> Int, ys: List<Int>): Int = List.fold(step, 0, ys)

                let total (i) = {
                    let chosen = if i.flag then add else sub
                    summed(chosen, i.xs) + summed(add, i.xs)
                }

                example total
                    | "t0" : (In { flag = true, xs = [] }) -> 0
                    | "t1" : (In { flag = true, xs = [1] }) -> 2
                    | "f0" : (In { flag = false, xs = [] }) -> 0
                    | "f1" : (In { flag = false, xs = [1] }) -> 0
                """.formatted(STEPS));

        assertEquals(LEFT_OPEN, foldVerdicts(compilation));
        assertEquals(List.of(), rewriteLines(compilation));
    }

    /** Each rewrite of each fold, by the definition that wrote the fold: how it stands. */
    private static List<String> verdictsByFold(Compilation compilation) {
        List<String> out = new ArrayList<>();
        JsonNode replacement = JSON.readTree(AdequacyReport.of(compilation)
                        .json(SourceRendering.namedByIdentity(compilation.texts())))
                .get("modules").get(0).get("behaviors").get(0).get("replacement");
        for (JsonNode each : replacement.get("obligations")) {
            JsonNode id = each.get("obligationId");
            if (id.get("rewrite").asString().startsWith("fold_")) {
                out.add(id.get("definition").asString() + " " + id.get("rewrite").asString()
                        + ": " + each.get("disposition").asString());
            }
        }
        return out.stream().sorted().toList();
    }

    /**
     * Two folds the language joins into one loop are two folds for what a row is asked: the rewrite
     * of one is the rewrite of that one. A {@code map} over a {@code filter} goes over what the
     * filter kept, so stopping the map after its first step stops it after the first element kept,
     * and a row the filter keeps one element of cannot tell that from the map going on. The loop the
     * two would be joined into stops after the first element of the list the filter goes over, which
     * is the filter stopping and tells nothing of the map.
     */
    @Test
    void aMapOverAFilterIsAskedOfTheMapAndOfTheFilterEachByItself() {
        Compilation compilation = measured("""
                module repro.chain

                behavior kept : (xs: List<Int>) -> List<Int>

                let kept (xs) = List.map(x -> x * 2, List.filter(x -> x > 1, xs))

                example kept
                    | "up" : ([1, 2]) -> [4]
                    | "down" : ([2, 1]) -> [4]
                """);

        assertEquals(List.of(
                        "filter fold_after_one_step: noticed",
                        "filter fold_from_the_seed: noticed",
                        "map fold_after_one_step: unnoticed",
                        "map fold_from_the_seed: unnoticed"),
                verdictsByFold(compilation));
    }

    private static String page(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static List<String> rewriteLines(Compilation compilation) {
        return page(compilation).lines().map(String::strip)
                .filter(line -> line.startsWith("! no row would come out differently"))
                .toList();
    }

    private static List<Located> rewriteWarnings(Compilation compilation) {
        return compilation.warnings().stream()
                .filter(each -> "E1939".equals(each.diagnostic().code().toString()))
                .toList();
    }

    private static Compilation measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(e -> e.diagnostic().code().toString()).toList(),
                "the model under test compiles");
        return compilation;
    }

    private static Compilation warned(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.warningsAt(Adequacy.Level.ALL));
        compilation.answerEverything();
        return compilation;
    }
}
