package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.PointRole;
import souther.compiler.partition.UndividedPosition;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ItemAssessment;
import souther.compiler.query.PartitionEvidence;

import java.util.Arrays;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An element of what a walk answering one value per element holds is the walk's step on one
 * element, and a rule about it is a rule about that.
 *
 * <p>{@code List.filter(c -> c >= atLeast, List.map(x -> x + 1, cs))} states {@code cs[*] + 1 >=
 * atLeast}, and the line it draws is on {@code cs[*]} one below {@code atLeast}. Which step it is
 * is read off the application that built the container, so two walks over one list are two
 * different rules — and an operation that does not answer one value per element, a set's
 * {@code map}, leaves its element an element and no more.
 *
 * <p>Where the element is left that way, the rule is still filed where its values came from, beside
 * the place it was filed at. That place keeps its own word: what a position whose values the rule
 * is about is left with is that position's, and is not changed by where the other side came from.
 */
class AnElementOfAWalksAnswerIsTheStepsAnswerOnOneElementTest {

    @Test
    void anElementOfAListsMapIsTheStepOnOneElement() {
        assertEquals(List.of("cs[*] = atLeast - 1"), linesOf("""
                behavior busy : (cs: List<Int>, atLeast: Int) -> List<Int>
                let busy (cs, atLeast) = List.filter(c -> c >= atLeast, List.map(x -> x + 1, cs))
                """));
    }

    /**
     * The line is measured where it is drawn: a row whose element is one below {@code atLeast}
     * meets the ON point and one two below meets OFF, through the walk and not around it.
     */
    @Test
    void aRowMeetsThePointsOfTheLineThroughTheWalk() {
        String model = """
                behavior busy : (cs: List<Int>, atLeast: Int) -> List<Int>
                let busy (cs, atLeast) = List.filter(c -> c >= atLeast, List.map(x -> x + 1, cs))

                example busy
                ROWS
                """;
        assertEquals(Set.of(PointRole.ON, PointRole.OFF), metIn(model.replace("ROWS", """
                    | "at the line" : ([2], 3) -> [3]
                    | "just off it" : ([1], 3) -> []
                """)));
        assertEquals(Set.of(PointRole.ON), metIn(model.replace("ROWS", """
                    | "at the line" : ([2], 3) -> [3]
                """)), "and a row at the line alone meets no OFF point");
    }

    /** {@code mapIndexed} hands its step the element beside its index, and the element is what
     *  arrives on the step's element parameter. */
    @Test
    void anIndexedWalksElementIsItsStepOnTheElement() {
        assertEquals(List.of("cs[*] = atLeast - 1"), linesOf("""
                behavior busy : (cs: List<Int>, atLeast: Int) -> List<Int>
                let busy (cs, atLeast) =
                    List.filter(c -> c >= atLeast, List.mapIndexed((i, x) -> x + 1, cs))
                """));
    }

    /** A step reading its index is about where the element stands in the list, which no position
     *  says: no line is drawn as though the index were not there. */
    @Test
    void anIndexedStepReadingItsIndexDrawsNoLineWithoutIt() {
        assertEquals(List.of(), linesOf("""
                behavior busy : (cs: List<Int>, atLeast: Int) -> List<Int>
                let busy (cs, atLeast) =
                    List.filter(c -> c >= atLeast, List.mapIndexed((i, x) -> x + i, cs))
                """));
    }

    @Test
    void aValueOfAMapsMappedValuesIsTheStepOnTheValueFiledThere() {
        assertEquals(List.of("m[*] = atLeast - 1"), linesOf("""
                behavior busy : (m: Map<String, Int>, atLeast: Int) -> Map<String, Int>
                let busy (m, atLeast) =
                    Map.filterEntries((_, count) -> count >= atLeast,
                        Map.mapValues((_, v) -> v + 1, m))
                """));
    }

    /** A step that is no arithmetic is read as whatever the reading of a number makes of it. A
     *  length is never below nought, so every {@code atLeast} at nought or below holds it whatever
     *  the string is, and is parted from the rest there. */
    @Test
    void aStepIsReadAsAnyExpressionIs() {
        assertEquals(List.of("atLeast = 0", "String.length(xs[*]) = atLeast"), linesOf("""
                behavior busy : (xs: List<String>, atLeast: Int) -> List<Int>
                let busy (xs, atLeast) =
                    List.filter(c -> c >= atLeast, List.map(x -> String.length(x), xs))
                """));
    }

    /** Two walks over one list are told apart by the application, and not by the list. */
    @Test
    void twoWalksOverOneListAreTwoSteps() {
        String model = """
                behavior busy : (cs: List<Int>, atLeast: Int) -> List<Int>
                let busy (cs, atLeast) = {
                    let a = List.map(x -> x + 1, cs)
                    let b = List.map(x -> x + 10, cs)
                    List.append(FIRST, SECOND)
                }
                """;
        assertEquals(List.of("cs[*] = atLeast - 1"), linesOf(model
                .replace("FIRST", "List.filter(c -> c >= atLeast, a)").replace("SECOND", "b")));
        assertEquals(List.of("cs[*] = atLeast - 10"), linesOf(model
                .replace("FIRST", "a").replace("SECOND", "List.filter(c -> c >= atLeast, b)")));
    }

    @Test
    void aWalkOverAWalkIsOneStepAfterTheOther() {
        assertEquals(List.of("-atLeast + 2 * cs[*] = -2"), linesOf("""
                behavior busy : (cs: List<Int>, atLeast: Int) -> List<Int>
                let busy (cs, atLeast) =
                    List.filter(c -> c >= atLeast, List.map(y -> y * 2, List.map(x -> x + 1, cs)))
                """));
    }

    /**
     * A set's {@code map} may answer one value for two elements, so an element of its answer is no
     * step on any one of them: no line, the rule filed at where the values came from, and the
     * position the rule is about left with its own word.
     */
    @Test
    void aWalkThatAnswersNoValuePerElementLeavesAnElement() {
        Compilation compilation = compiled("""
                behavior busy : (cs: Set<Int>, atLeast: Int) -> Set<Int>
                let busy (cs, atLeast) = Set.filter(c -> c >= atLeast, Set.map(x -> x + 1, cs))
                """);
        assertEquals(List.of(), linesOf(compilation));
        List<String> notRead = notReadIn(compilation);
        assertTrue(notRead.contains("cs[*] " + UndividedPosition.Reason.RULE_ABOUT_A_DERIVED_VALUE),
                () -> "filed where the values came from: " + notRead);
        assertEquals(List.of("atLeast " + UndividedPosition.Reason.UNSUPPORTED_SYNTAX),
                notRead.stream().filter(each -> each.startsWith("atLeast ")).toList(),
                "and the position the rule is about keeps its own word");
    }

    /**
     * A filter's closure is handed every element and answers whether to keep it, and what the
     * filter holds is the elements kept: an element of it is the element, and not what the closure
     * answered on it. The outer comparison draws its line on the element as it stands, beside the
     * line the inner filter draws.
     */
    @Test
    void anElementAFilterKeptIsNoStep() {
        assertEquals(List.of("cs[*] = 0", "cs[*] = atLeast"), linesOf("""
                behavior busy : (cs: List<Int>, atLeast: Int) -> List<Int>
                let busy (cs, atLeast) =
                    List.filter(c -> c >= atLeast, List.filter(x -> x > 0, cs))
                """));
    }

    /**
     * A map updated under one key holds the closure's answer on the value there and the values that
     * were there everywhere else, so a value of it is no step on the value it came from: the closure
     * is applied to one value at most, and no line is drawn as though it were applied to each.
     */
    @Test
    void aValueOfAMapUpdatedUnderOneKeyIsNoStep() {
        assertEquals(List.of(), linesOf("""
                behavior busy : (m: Map<String, Int>, atLeast: Int) -> Map<String, Int>
                let busy (m, atLeast) =
                    Map.filterEntries((_, count) -> count >= atLeast,
                        Map.updateIfPresent("a", v -> v + 1, m))
                """));
    }

    /**
     * A value a fold files under a key is no step on an element of the list folded, but how often
     * the key occurs among them: the line is drawn on that and the position it is compared with is
     * read against it.
     */
    @Test
    void aCounterAFoldFilesUnderEachKeyIsHowOftenTheKeyOccurs() {
        Compilation compilation = compiled("""
                let countsOf (xs: List<String>): Map<String, Int> =
                    List.fold((acc, x) -> Map.updateOrInsert(x, 1, n -> n + 1, acc), Map.empty, xs)

                behavior busy : (xs: List<String>, atLeast: Int) -> Map<String, Int>
                let busy (xs, atLeast) =
                    Map.filterEntries((_, count) -> count >= atLeast, countsOf(xs))
                """);
        assertEquals(List.of("atLeast - multiplicity(xs[*]) = 0"), linesOf(compilation));
        assertEquals(List.of("atLeast "
                        + UndividedPosition.Reason.RELATION_NOT_SHOWN_TO_REACH_EVERY_VALUE),
                notReadIn(compilation).stream().filter(each -> each.startsWith("atLeast ")).toList(),
                "the position the rule is about is related to how often the key occurs, which is"
                        + " not shown to reach every value of it");
    }

    /**
     * A value a fold worked out that is no counter is no step on an element of the list folded: the
     * position it is compared with keeps its own word and is told nothing about a value made from
     * it.
     */
    @Test
    void aValueAFoldWorkedOutIsNoStep() {
        Compilation compilation = compiled("""
                let countsOf (xs: List<String>): Map<String, Int> =
                    List.fold((acc, x) -> Map.updateOrInsert(x, 0, n -> 127 - n, acc), Map.empty, xs)

                behavior busy : (xs: List<String>, atLeast: Int) -> Map<String, Int>
                let busy (xs, atLeast) =
                    Map.filterEntries((_, count) -> count >= atLeast, countsOf(xs))
                """);
        assertEquals(List.of(), linesOf(compilation));
        List<String> notRead = notReadIn(compilation);
        assertEquals(List.of("atLeast " + UndividedPosition.Reason.UNSUPPORTED_SYNTAX),
                notRead.stream().filter(each -> each.startsWith("atLeast ")).toList(),
                () -> "the position the rule is about keeps its own word: " + notRead);
    }

    /**
     * A rule about a value such a fold worked out, comparing it with nothing of the input, is
     * still a rule: it is not read, and is said to be about a value made of the list the fold
     * walked — whether the value is an entry handed by a walk over the map or one a lookup under
     * the map's own keys found.
     */
    @Test
    void aRuleAboutAValueAFoldWorkedOutIsNotReadAtTheListItWalked() {
        String fold = """
                let countsOf (xs: List<String>): Map<String, Int> =
                    List.fold((acc, x) -> Map.updateOrInsert(x, 0, n -> 127 - n, acc), Map.empty, xs)

                """;
        for (String busy : List.of("""
                behavior busy : (xs: List<String>) -> Map<String, Int>
                let busy (xs) = Map.filterEntries((_, count) -> count >= 3, countsOf(xs))
                """, """
                behavior busy : (xs: List<String>) -> List<String>
                let busy (xs) = {
                    let counts = countsOf(xs)
                    List.filter(x -> match Map.get(x, counts) with
                                        | Some count -> count >= 3
                                        | None -> false, Map.keys(counts))
                }
                """)) {
            List<String> notRead = notReadIn(compiled(fold + busy));
            assertEquals(List.of("xs[*] " + UndividedPosition.Reason.RULE_ABOUT_A_DERIVED_VALUE),
                    notRead, () -> busy);
        }
    }

    /**
     * A fold starting from a map the input holds is made of that map as well as of the list it
     * walked — over an empty list it answers the map itself — so a value of it is not said to have
     * come from the list alone: a rule about it is about a value made of both.
     */
    @Test
    void aValueAFoldFromAnInputMapWorkedOutIsSaidToBeMadeOfBothTheMapAndTheList() {
        List<String> notRead = notReadIn(compiled("""
                let countsOf (start: Map<String, Int>, xs: List<String>): Map<String, Int> =
                    List.fold((acc, x) -> Map.updateOrInsert(x, 0, n -> 127 - n, acc), start, xs)

                behavior busy : (start: Map<String, Int>, xs: List<String>) -> Map<String, Int>
                let busy (start, xs) =
                    Map.filterEntries((_, count) -> count >= 3, countsOf(start, xs))

                example busy
                    | "nothing walked, the start kept" : ([("a", 5), ("b", 1)], []) -> [("a", 5)]
                """));
        assertEquals(List.of("start[*] " + UndividedPosition.Reason.RULE_ABOUT_A_DERIVED_VALUE,
                        "xs[*] " + UndividedPosition.Reason.RULE_ABOUT_A_DERIVED_VALUE),
                notRead, () -> notRead.toString());
    }

    private static final String SEEDED_FOLD = """
            let countsOf (start: Map<String, Int>, xs: List<String>): Map<String, Int> =
                List.fold((acc, x) -> Map.updateOrInsert(x, 0, n -> 127 - n, acc), start, xs)

            """;

    /** Everything the measurement does not read, whatever the reason. */
    private List<String> notReadWith(String behavior) {
        return notReadIn(compiled(SEEDED_FOLD + behavior)).stream().sorted().toList();
    }

    private static List<String> derivedAt(String... positions) {
        return Arrays.stream(positions)
                .map(each -> each + " " + UndividedPosition.Reason.RULE_ABOUT_A_DERIVED_VALUE)
                .sorted().toList();
    }

    /** A choice between two values each made of two places keeps all four. */
    @Test
    void aChoiceBetweenTwoValuesEachMadeOfTwoInputsIsMadeOfAllFour() {
        assertEquals(derivedAt("other[*]", "start[*]", "xs[*]", "ys[*]"), notReadWith("""
                behavior busy : (flag: Bool, start: Map<String, Int>, other: Map<String, Int>, xs: List<String>, ys: List<String>) -> Map<String, Int>
                let busy (flag, start, other, xs, ys) =
                    Map.filterEntries((_, count) -> count >= 3,
                        if flag then countsOf(start, xs) else countsOf(other, ys))
                """));
    }

    /** A fold over a list chosen between two is made of the seed and of either list. */
    @Test
    void aFoldFromAnInputMapOverAListChosenBetweenTwoIsMadeOfTheMapAndEitherList() {
        assertEquals(derivedAt("start[*]", "xs[*]", "ys[*]"), notReadWith("""
                behavior busy : (flag: Bool, start: Map<String, Int>, xs: List<String>, ys: List<String>) -> Map<String, Int>
                let busy (flag, start, xs, ys) =
                    Map.filterEntries((_, count) -> count >= 3,
                        countsOf(start, if flag then xs else ys))
                """));
    }

    /**
     * A seed worked out of an input number stands at no position, and what it was worked out of is
     * not followed through arithmetic: the rule is said at the list the fold walked, which it is
     * made of, and not at the number, which it is too — over an empty list the answer is the seed.
     * Pinned so that the limit is a fact somebody wrote down, and the answer is not taken for the
     * whole of where the value came from.
     */
    @Test
    void aFoldFromASeedWorkedOutOfAnInputNumberIsSaidAtTheListAndNotFollowedToTheNumber() {
        assertEquals(derivedAt("xs[*]"), notReadIn(compiled("""
                let countsOf (n: Int, xs: List<String>): Map<String, Int> =
                    List.fold((acc, x) -> Map.updateOrInsert(x, 0, c -> 127 - c, acc),
                              Map.fromList([("k", n + 1)]), xs)

                behavior busy : (n: Int, xs: List<String>) -> Map<String, Int>
                let busy (n, xs) =
                    Map.filterEntries((_, count) -> count >= 3, countsOf(n, xs))
                """)).stream().sorted().toList());
    }

    /** A fold seeded with what another fold made is made of all that fold was made of. */
    @Test
    void aFoldSeededWithAValueAFoldMadeIsMadeOfEverythingBothWereMadeOf() {
        assertEquals(derivedAt("start[*]", "xs[*]", "ys[*]"), notReadWith("""
                behavior busy : (start: Map<String, Int>, xs: List<String>, ys: List<String>) -> Map<String, Int>
                let busy (start, xs, ys) =
                    Map.filterEntries((_, count) -> count >= 3,
                        countsOf(countsOf(start, xs), ys))
                """));
    }

    /**
     * A field of a value made of an input map's entries and of the list a fold walked is made of
     * those, and not of a field of the list's elements, which have none.
     */
    @Test
    void aFieldOfAValueMadeOfTwoInputsIsMadeOfThemAndNamesNoFieldOfEither() {
        assertEquals(derivedAt("start[*]", "xs[*]"), notReadIn(compiled("""
                data Counter = { count: Int }

                let tally (start: Map<String, Counter>, xs: List<String>): Map<String, Counter> =
                    List.fold((acc, x) -> Map.updateOrInsert(x, Counter { count = 0 },
                                                             c -> Counter { count = 127 - c.count }, acc),
                              start, xs)

                behavior busy : (start: Map<String, Counter>, xs: List<String>) -> Map<String, Counter> constructs Counter
                let busy (start, xs) =
                    Map.filterEntries((_, c) -> c.count >= 3, tally(start, xs))
                """)));
    }

    private static final String COUNTS_OF = """
            let countsOf (xs: List<String>): Map<String, Int> =
                List.fold((acc, x) -> Map.updateOrInsert(x, 1, n -> 127 - n, acc), Map.empty, xs)

            """;

    /** A pair taken out of a pair is read to the end, however many pairs deep the value is. */
    @Test
    void aValueTakenOutOfAPairTakenOutOfAPairComesFromWhereTheHelperGotIt() {
        assertEquals(derivedAt("xs[*]"), notReadIn(compiled(COUNTS_OF + """
                let boxed (m: Map<String, Int>): ((Int, Map<String, Int>), Int) = ((0, m), 1)

                behavior busy : (xs: List<String>) -> Map<String, Int>
                let busy (xs) = {
                    let (inner, _) = boxed(countsOf(xs))
                    let (_, selected) = inner
                    Map.filterEntries((_, count) -> count >= 3, selected)
                }
                """)).stream().sorted().toList());
    }

    /** What a record was given for a field is what a field read back out of it holds. */
    @Test
    void aFieldOfARecordHoldsWhatTheRecordWasGivenForIt() {
        assertEquals(derivedAt("xs[*]"), notReadIn(compiled(COUNTS_OF + """
                data Box = { m: Map<String, Int> }

                behavior busy : (xs: List<String>) -> Map<String, Int> constructs Box
                let busy (xs) = {
                    let box = Box { m = countsOf(xs) }
                    Map.filterEntries((_, count) -> count >= 3, box.m)
                }
                """)).stream().sorted().toList());
    }

    /** A field of a record a helper chose between is the field of whichever it chose. */
    @Test
    void aFieldOfARecordAHelperChoseBetweenComesFromEitherPlace() {
        List<String> notRead = notReadIn(compiled(COUNTS_OF + """
                data Box = { m: Map<String, Int> }

                let pickBox (flag: Bool, a: Map<String, Int>, b: Map<String, Int>): Box =
                    if flag then Box { m = a } else Box { m = b }

                behavior busy : (flag: Bool, xs: List<String>, ys: List<String>) -> Map<String, Int>
                    constructs Box
                let busy (flag, xs, ys) = {
                    let box = pickBox(flag, countsOf(xs), countsOf(ys))
                    Map.filterEntries((_, count) -> count >= 3, box.m)
                }
                """));
        assertEquals(2, notRead.stream().filter(each -> each.startsWith("xs[*] ")
                || each.startsWith("ys[*] ")).count(), () -> notRead.toString());
    }

    private static final String WHICH = """
            data Left = { items: Map<String, Int> }
            data Right = { count: Int }
            data Which = Left | Right

            """;

    /** What is left unread when the rule's own number is all that is: no position it is about. */
    private static final String ONLY_THE_NUMBER_UNREAD =
            "[atLeast " + UndividedPosition.Reason.UNSUPPORTED_SYNTAX + "]";

    /**
     * A name an arm of a match binds is read where the arm is entered, and a value that reads one
     * is followed no further out. Entering an arm is the walks' own
     * ({@code ScopeStep.Chosen}, {@code InputReads#choosing}), and it needs what a position's
     * query does not hold. So a pair or a record a helper answers out of such an arm is no
     * position, where the same rule written inside the arm draws its line. Pinned so that the
     * limit is a fact somebody wrote down, and so that the day a query can enter an arm it is a
     * test that changes.
     */
    @Test
    void aNameAMatchArmBindsIsNotFollowedOutOfTheArmItWasBoundIn() {
        assertEquals(List.of("w@Left.items[*] = atLeast"), linesOf(WHICH + """
                behavior busy : (w: Which, atLeast: Int) -> Map<String, Int>
                let busy (w, atLeast) =
                    match w with
                    | Left as l -> Map.filterEntries((_, count) -> count >= atLeast, l.items)
                    | Right -> Map.empty
                """), "inside the arm the rule draws its line");

        Compilation pair = compiled(WHICH + """
                let select (w: Which): (Int, Map<String, Int>) =
                    match w with
                    | Left as l -> (1, l.items)
                    | Right -> (0, Map.empty)

                behavior busy : (w: Which, atLeast: Int) -> Map<String, Int>
                let busy (w, atLeast) = {
                    let (_, selected) = select(w)
                    Map.filterEntries((_, count) -> count >= atLeast, selected)
                }
                """);
        assertEquals(List.of(), linesOf(pair));
        assertEquals(ONLY_THE_NUMBER_UNREAD, notReadIn(pair).stream().sorted().toList().toString());

        Compilation record = compiled(WHICH + """
                data Box = { m: Map<String, Int> }

                let select (w: Which): Box =
                    match w with
                    | Left as l -> Box { m = l.items }
                    | Right -> Box { m = Map.empty }

                behavior busy : (w: Which, atLeast: Int) -> Map<String, Int> constructs Box
                let busy (w, atLeast) = {
                    let box = select(w)
                    Map.filterEntries((_, count) -> count >= atLeast, box.m)
                }
                """);
        assertEquals(List.of(), linesOf(record));
        assertEquals(ONLY_THE_NUMBER_UNREAD, notReadIn(record).stream().sorted().toList().toString());
    }

    /** Which pair a match chose is read in every arm, one of which binds a name of its own. */
    @Test
    void aValueTakenOutOfAPairAMatchChoseBetweenComesFromEitherArm() {
        List<String> notRead = notReadIn(compiled(COUNTS_OF + """
                let pick (o: Option<Int>, a: Map<String, Int>, b: Map<String, Int>)
                        : (Int, Map<String, Int>) =
                    match o with
                    | Some v -> (v, a)
                    | None -> (0, b)

                behavior busy : (xs: List<String>, ys: List<String>) -> Map<String, Int>
                let busy (xs, ys) = {
                    let (_, m) = pick(Map.get("k", countsOf(xs)), countsOf(xs), countsOf(ys))
                    Map.filterEntries((_, count) -> count >= 3, m)
                }
                """));
        assertEquals(2, notRead.stream().filter(each -> each.startsWith("xs[*] ")
                || each.startsWith("ys[*] ")).count(), () -> notRead.toString());
    }

    /** A value taken out of a pair a helper chose between is the component of whichever it chose. */
    @Test
    void aValueTakenOutOfAPairAHelperChoseBetweenComesFromEitherPlace() {
        List<String> notRead = notReadIn(compiled("""
                let countsOf (xs: List<String>): Map<String, Int> =
                    List.fold((acc, x) -> Map.updateOrInsert(x, 1, n -> 127 - n, acc), Map.empty, xs)

                let pick (flag: Bool, a: Map<String, Int>, b: Map<String, Int>)
                        : (Int, Map<String, Int>) =
                    if flag then (1, a) else (2, b)

                behavior busy : (flag: Bool, xs: List<String>, ys: List<String>) -> List<String>
                let busy (flag, xs, ys) = {
                    let (_, m) = pick(flag, countsOf(xs), countsOf(ys))
                    List.filter(a -> match Map.get(a, m) with
                                        | Some n -> n > 1
                                        | None -> false, Map.keys(m))
                }
                """));
        assertEquals(2, notRead.stream().filter(each -> each.startsWith("xs[*] ")
                || each.startsWith("ys[*] ")).count(), () -> notRead.toString());
    }

    /**
     * A fold whose answer holds lists, flattened, is made of the lists it was seeded with and of the
     * strings it walked, and a rule about it is said at those two.
     */
    @Test
    void aFlattenedFoldMadeOfListsAndStringsIsSaidAtBoth() {
        List<String> notRead = notReadIn(compiled("""
                let listsOf (start: Map<String, List<Int>>, xs: List<String>): Map<String, List<Int>> =
                    List.fold((acc, x) -> Map.updateOrInsert(x, [], l -> List.reverse(l), acc),
                              start, xs)

                behavior busy : (start: Map<String, List<Int>>, xs: List<String>) -> List<Int>
                let busy (start, xs) =
                    List.filter(n -> n >= 3, List.flatMap(l -> l, Map.values(listsOf(start, xs))))
                """));
        assertEquals(derivedAt("start[*]", "xs[*]"), notRead.stream().sorted().toList());
    }

    /** A value taken out of a pair a helper built is the component the helper put there. */
    @Test
    void aValueTakenOutOfAPairAHelperBuiltComesFromWhereTheHelperGotIt() {
        List<String> notRead = notReadIn(compiled("""
                let countsOf (xs: List<String>): Map<String, Int> =
                    List.fold((acc, x) -> Map.updateOrInsert(x, 1, n -> 127 - n, acc), Map.empty, xs)

                let split (m: Map<String, Int>): (List<String>, Map<String, Int>) = (Map.keys(m), m)

                behavior busy : (xs: List<String>, ys: List<String>) -> List<String>
                let busy (xs, ys) = {
                    let (ka, _) = split(countsOf(xs))
                    let (_, mb) = split(countsOf(ys))
                    List.filter(a -> match Map.get(a, mb) with
                                        | Some n -> n > 1
                                        | None -> false, ka)
                }
                """));
        assertEquals(List.of("ys[*] " + UndividedPosition.Reason.RULE_ABOUT_A_DERIVED_VALUE),
                notRead, () -> notRead.toString());
    }

    /** A rule about the strings such a fold worked out is a rule all the same, and is said to be
     *  about values made of the list the fold walked. */
    @Test
    void aStringRuleAboutAValueAFoldWorkedOutIsNotReadAtTheListItWalked() {
        List<String> notRead = notReadIn(compiled("""
                let tagsOf (xs: List<String>): Map<String, String> =
                    List.fold((acc, x) -> Map.updateOrInsert(x, x, v -> String.append(v, "!"), acc), Map.empty, xs)

                behavior busy : (xs: List<String>) -> Map<String, String>
                let busy (xs) = Map.filterEntries((_, v) -> String.startsWith("a", v), tagsOf(xs))
                """));
        assertEquals(List.of("xs[*] " + UndividedPosition.Reason.RULE_ABOUT_A_DERIVED_VALUE),
                notRead, () -> notRead.toString());
    }

    @Test
    void aValueOfAMapMadeOfAListsMapIsTheSecondComponentOfTheStep() {
        assertEquals(List.of("atLeast = 1"), linesOf("""
                behavior busy : (xs: List<String>, atLeast: Int) -> Map<String, Int>
                let busy (xs, atLeast) =
                    Map.filterEntries((_, c) -> c >= atLeast,
                        Map.fromList(List.map(x -> (x, 1), xs)))
                """));
    }

    /**
     * Entries filed under one key leave the last of them, so a value an earlier entry carried is
     * compared with nothing. A row whose first element sits on the line has not put the comparison
     * on it, and no line is drawn on a value the map may not hold.
     */
    @Test
    void anEntryAnotherReplacedIsNotTheValueTheComparisonRuns() {
        String model = """
                behavior busy : (xs: List<Int>, atLeast: Int) -> Map<String, Int>
                let busy (xs, atLeast) =
                    Map.filterEntries((_, c) -> c >= atLeast,
                        Map.fromList(List.map(x -> ("fixed", x), xs)))

                example busy
                    | "the first is replaced" : ([3, 1], 3) -> []
                """;
        assertEquals(List.of(), linesOf(model));
        assertEquals(Set.of(), metIn(model));
    }

    /** One value for every element, whatever the key is. */
    @Test
    void aValueNoElementChangesIsReadWhateverTheKeyIs() {
        assertEquals(List.of("atLeast = 1"), linesOf("""
                behavior busy : (xs: List<String>, atLeast: Int) -> Map<String, Int>
                let busy (xs, atLeast) =
                    Map.filterEntries((_, c) -> c >= atLeast,
                        Map.fromList(List.map(x -> (String.trim(x), 1), xs)))
                """));
    }

    /** Elements that differ may be filed under one key while carrying different values, and
     *  nothing here shows the key to be what fixes the value. */
    @Test
    void aValueAKeyThatIsNotTheElementDoesNotFixIsNotRead() {
        assertEquals(List.of(), linesOf("""
                behavior busy : (xs: List<String>, atLeast: Int) -> Map<String, Int>
                let busy (xs, atLeast) =
                    Map.filterEntries((_, c) -> c >= atLeast,
                        Map.fromList(List.map(x -> (String.trim(x), String.length(x)), xs)))
                """));
    }

    /** The key being the element is not enough: the index differs between equal elements, so the
     *  entry that is left holds a value the replaced one did not. */
    @Test
    void aValueTheIndexDecidesIsNotFixedByTheKey() {
        assertEquals(List.of(), linesOf("""
                behavior busy : (xs: List<String>, atLeast: Int) -> Map<String, Int>
                let busy (xs, atLeast) =
                    Map.filterEntries((_, c) -> c >= atLeast,
                        Map.fromList(List.mapIndexed((i, x) -> (x, i), xs)))
                """));
    }

    /** Equal elements are filed under one key and carry one value, so a row of them still meets
     *  both sides of the line. */
    @Test
    void equalElementsFiledUnderOneKeyStillMeetBothSidesOfTheLine() {
        assertEquals(Set.of(PointRole.ON, PointRole.OFF), metIn("""
                behavior busy : (xs: List<String>, atLeast: Int) -> Map<String, Int>
                let busy (xs, atLeast) =
                    Map.filterEntries((_, c) -> c >= atLeast,
                        Map.fromList(List.map(x -> (x, 1), xs)))

                example busy
                    | "twice at the line" : (["a", "a"], 1) -> [("a", 1)]
                    | "twice just off it" : (["a", "a"], 2) -> []
                """));
    }

    /** The line is measured through the map: a row at the line meets ON and one a step off meets
     *  OFF, which is the comparison being run on both sides. */
    @Test
    void aRowMeetsThePointsOfALineDrawnThroughAMapMadeOfAListsMap() {
        String model = """
                behavior busy : (xs: List<String>, atLeast: Int) -> Map<String, Int>
                let busy (xs, atLeast) =
                    Map.filterEntries((_, c) -> c >= atLeast,
                        Map.fromList(List.map(x -> (x, 1), xs)))

                example busy
                ROWS
                """;
        assertEquals(Set.of(PointRole.ON, PointRole.OFF), metIn(model.replace("ROWS", """
                    | "at the line" : (["a"], 1) -> [("a", 1)]
                    | "just off it" : (["a"], 2) -> []
                """)));
    }

    /** The second component is an expression like any other, and the line is drawn on what it
     *  reads. */
    @Test
    void theSecondComponentIsReadAsAnyExpressionIs() {
        assertEquals(List.of("String.length(xs[*]) = atLeast - 1"), linesOf("""
                behavior busy : (xs: List<String>, atLeast: Int) -> Map<String, Int>
                let busy (xs, atLeast) =
                    Map.filterEntries((_, c) -> c >= atLeast,
                        Map.fromList(List.map(x -> (x, String.length(x) + 1), xs)))
                """));
    }

    /** What the key is filed under is the first component and is no part of what is read. */
    @Test
    void theKeyOfAMapMadeOfAListsMapIsNotTheValue() {
        assertEquals(List.of(), linesOf("""
                behavior busy : (xs: List<String>, atLeast: Int) -> Map<String, Int>
                let busy (xs, atLeast) =
                    Map.filterEntries((k, _) -> String.length(k) >= atLeast,
                        Map.fromList(List.map(x -> (x, 1), xs)))
                """));
    }

    /** Entries that are not the answer of one walk give no step to read the value as. */
    @Test
    void entriesNoSingleWalkMadeLeaveAnElement() {
        assertEquals(List.of(), linesOf("""
                behavior busy : (xs: List<String>, atLeast: Int) -> Map<String, Int>
                let busy (xs, atLeast) =
                    Map.filterEntries((_, c) -> c >= atLeast,
                        Map.fromList(List.append([("a", 1)], List.map(x -> (x, 2), xs))))
                """));
    }

    /** Every line the comparison in {@code body} draws, as its label. */
    private static List<String> linesOf(String body) {
        return linesOf(compiled(body));
    }

    private static List<String> linesOf(Compilation compilation) {
        return Adequacy.readingsOf(compilation.db(), "probe").get("busy").stream()
                .map(BorderAssessment::label)
                .toList();
    }

    /** Which points of the lines in {@code body} a row of its examples met. */
    private static Set<PointRole> metIn(String body) {
        Compilation compilation = compiled(body);
        Set<PointRole> met = new TreeSet<>();
        for (BorderAssessment.Point point : BorderAssessment.pointsOf(
                Adequacy.readingsOf(compilation.db(), "probe").get("busy"))) {
            if (point.owed() != null && point.owed().coverage().made().orElseThrow()
                    instanceof ItemAssessment.Coverage.Hit) {
                met.add(point.role());
            }
        }
        return met;
    }

    /** Every place the rules of what was compiled were not read at, with the reason. */
    private static List<String> notReadIn(Compilation compilation) {
        PartitionEvidence measured = compilation.db()
                .ask(new Adequacy.Coverage("probe")).value().get("busy");
        return measured.notRead().stream()
                .map(each -> each.at() + " " + each.reason())
                .toList();
    }

    private static Compilation compiled(String body) {
        Compilation compilation = Compilation.ofSource("module probe\n\n" + body, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model compiles");
        return compilation;
    }
}
