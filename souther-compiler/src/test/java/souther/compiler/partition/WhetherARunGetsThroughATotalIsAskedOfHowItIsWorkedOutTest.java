package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.StatedComparison;
import souther.compiler.diag.SourceRendering;
import souther.compiler.inputs.Denotation;
import souther.compiler.inputs.WhatARelationLeavesUndivided;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Whether a run gets through a total is a claim about how the total is worked out, and not about
 * the number it comes to (ADR-0125). With {@code MAX} the greatest {@code Int}: a sum of
 * {@code [MAX, 1, -1]} holds only its total to the type and gets through; a fold adding the same
 * numbers one step at a time stops at its second step; a total of what doubling makes of
 * {@code [MAX, -MAX]} comes to nought and stops at the first doubling. So none of the three is
 * given another's evidence.
 *
 * <p>Where the elements are not written out, the applications of a closure or the steps of a walk
 * cannot be listed. They are shown to get through only by one statement about every one of them,
 * and are otherwise neither shown to get through nor shown to stop.
 */
class WhetherARunGetsThroughATotalIsAskedOfHowItIsWorkedOutTest {

    private static final String MAX = "9223372036854775807";

    private static final String NAT = "data Nat = Int invariant value >= 0";

    private static final String UNUSED = "data Unused = Int";

    private static String report(String inputs, String declarations, String body) {
        Compilation compilation = Compilation.ofSource("""
                module w1
                %s
                behavior m : (%s) -> Bool
                let m (%s) = %s
                """.formatted(declarations, inputs, inputs.replaceAll(": (Map<[^>]*>|[A-Za-z<>]+)", ""), body),
                "Main");
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model under test compiles");
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    /** Where every run is shown to stop, as the report says it; empty where it says nothing. */
    private static String whereEveryRunStops(String report) {
        return report.lines().filter(line -> line.contains("every run stops"))
                .map(line -> line.substring(line.indexOf("every run stops")))
                .collect(Collectors.joining("\n"));
    }

    /** The places the report says the comparison relates rather than divides. */
    private static Set<String> related(String report) {
        return placesSaying(report, "· no line", "rather than dividing the values here");
    }

    /** The places the report says the comparison relates to a value not shown to reach them. */
    private static Set<String> notShown(String report) {
        return placesSaying(report, "· not read", "not shown to reach every value here");
    }

    private static Set<String> placesSaying(String report, String start, String words) {
        return report.lines().map(String::strip)
                .filter(line -> line.startsWith(start) && line.contains(words))
                .map(line -> line.substring(line.lastIndexOf("about `") + 7, line.length() - 1))
                .collect(Collectors.toSet());
    }

    @Test
    void aSumGetsThroughWhereAFoldOfTheSameNumbersStopsAtAStep() {
        String inputs = "n: Int, k: Int";
        String sum = report(inputs, UNUSED, "List.sum([n, 1, -1]) >= k");
        String fold = report(inputs, UNUSED, "List.fold((acc, x) -> acc + x, 0, [n, 1, -1]) >= k");
        assertEquals("", whereEveryRunStops(sum), sum);
        assertEquals("every run stops in n + 1 where n is at least " + MAX,
                whereEveryRunStops(fold), fold);
    }

    /**
     * Over a list reached by a name the walk is read for the total it comes to by the rule that
     * follows the name, and its steps are in no tree the comparison is read through: no row is
     * shown to get through them, and the walk is not taken to add the form up and nothing else.
     */
    @Test
    void aFoldOverAListReachedByANameIsNotTakenToGetThroughWhereItsAnswerIsAnInt() {
        String report = report("n: Int, k: Int", UNUSED, """
                {
                    let xs = [n, 1, -1]
                    List.fold((acc, x) -> acc + x, 0, xs) >= k
                }""");
        assertEquals(Set.of(), related(report), report);
        assertEquals(Set.of("k", "n"), notShown(report), report);
    }

    /** Where doubling an {@code Int} at or past {@code from} passes the type, from above and
     *  from below, as the report says it of {@code doubled}. */
    private static String whereDoublingStops(String doubled) {
        long least = Long.MAX_VALUE / 2 + 1;
        return "every run stops in 2 * " + doubled + " where " + doubled + " is at least " + least
                + ", in 2 * " + doubled + " where " + doubled + " is at most " + (-least - 1);
    }

    /**
     * A value a binding gives a name is worked out before the body whether or not the body
     * reads it. Bound and never read, in a closure applied to each element of a list written out
     * or in the step of a walk over one, it still stops the run where it passes the type, though
     * what the total or the walk comes to does not.
     */
    @Test
    void aValueBoundAndNeverReadStillStopsTheRun() {
        String inputs = "n: Int, k: Int";
        String mapped = report(inputs, UNUSED, """
                List.sum(List.map(x -> {
                        let discarded = 2 * x
                        x
                    }, [n])) >= k""");
        assertEquals(whereDoublingStops("n"), whereEveryRunStops(mapped), mapped);
        String walked = report(inputs, UNUSED, """
                List.fold((acc, x) -> {
                        let discarded = 2 * x
                        acc + x
                    }, 0, [n]) >= k""");
        assertEquals(whereDoublingStops("n"), whereEveryRunStops(walked), walked);
    }

    /**
     * Over a container, a value bound and never read is no part of what the closure answers, so
     * it is not between nought and the total: doubled, it passes the type at an element the
     * total holds. Bound and read, it is part of the answer, and the total is left either way.
     */
    @Test
    void aValueBoundInAClosureIsNoMoreThanTheTotalOnlyWhereTheClosureReadsIt() {
        String inputs = "gross: Int, ns: List<Nat>";
        String discarded = report(inputs, NAT, """
                gross >= List.sum(List.map(n -> {
                        let discarded = 2 * n.value
                        n.value
                    }, ns))""");
        assertEquals(Set.of("List.sum(ns[*])", "gross"), notShown(discarded), discarded);
        String doubled = report(inputs, NAT, """
                gross >= List.sum(List.map(n -> {
                        let doubled = 2 * n.value
                        doubled
                    }, ns))""");
        assertTrue(related(doubled).contains("List.sum({2·the element itself + 0 | ns[*]})"),
                doubled);
    }

    /**
     * A helper's arguments are worked out before its body, whichever of them the body reads, and
     * whichever arm it takes: one it never reads, or reads only in the other arm, stops the run
     * where it passes the type, and the comparison of what it answers is not taken to get
     * through there.
     */
    @Test
    void anArgumentAHelperDoesNotReadStillStopsTheRun() {
        String unread = report("n: Int, m: Int, k: Int",
                UNUSED + "\nlet first (a: Int, b: Int) : Int = a", "first(n, 2 * m) >= k");
        assertEquals(whereDoublingStops("m"), whereEveryRunStops(unread), unread);
        assertEquals(Set.of(), related(unread), unread);
        String inAnArm = report("flag: Bool, n: Int, m: Int, k: Int",
                UNUSED + "\nlet pick (c: Bool, a: Int, b: Int) : Int = if c then a else b",
                "pick(flag, 2 * m, n) >= k");
        assertFalse(related(inAnArm).contains("n"), inAnArm);
        assertTrue(notShown(inAnArm).contains("n"), inAnArm);
    }

    /** What the comparison {@code condition} of a behavior taking {@code inputs} works out, read
     *  off the tree a module's comparisons are read off when it is measured. */
    private static UndividedByARelation.Working workingOf(String inputs, String condition) {
        ReadComparisons read = ReadComparisons.ofTheAnalysis("""
                module w1
                data Unused = Int
                behavior m : (%s) -> Bool
                let m (%s) = %s
                """.formatted(inputs, inputs.replaceAll(": [A-Za-z<>]+", ""), condition), "m");
        ComparisonReadings.Reading only = read.only();
        AffineReading.OfAComparison arithmetic = AffineReading.read(
                ((ComparisonReadings.Stated.AComparison) only.statement()).comparison(),
                only.reads(), read.inputs().reading(read.rules()));
        return AffineReading.OfAComparison.workingOf(arithmetic);
    }

    /**
     * A value bound and never read that comes to a form, though working it out is not shown to
     * get through, is still worked out: the total of {@code x + 1 - 1} over {@code ns} comes to
     * the total of {@code ns} and stops at the greatest {@code Int}. The comparison beside it is
     * not taken to tell every operation its rows get past, as it is with no such binding.
     */
    @Test
    void aValueThatComesToAFormIsNotTakenToGetThroughForThat() {
        String inputs = "ns: List<Int>, n: Int, k: Int";
        UndividedByARelation.Working bound = workingOf(inputs, """
                ({
                    let unread = List.sum(List.map(x -> x + 1 - 1, ns))
                    n
                }) >= k""");
        assertEquals(WhatARelationLeavesUndivided.Told.SOME, bound.told(), bound::toString);
        UndividedByARelation.Working alone = workingOf(inputs, "n >= k");
        assertEquals(WhatARelationLeavesUndivided.Told.EVERY, alone.told(), alone::toString);
    }

    /**
     * A walk read after other operations of the comparison is worked out after them, and each
     * step after the one before: the step that adds {@code j} is worked out of the step that
     * added {@code m}, and not of the sum the comparison worked out first.
     */
    @Test
    void eachStepOfAWalkReadAfterOtherOperationsIsWorkedOutOfTheStepBefore() {
        UndividedByARelation.Working whole = workingOf("n: Int, m: Int, j: Int, k: Int",
                "k + 1 >= List.fold((acc, x) -> acc + x, 0, [n, m, j])");
        List<UndividedByARelation.IntOperation> told = whole.operations();
        assertFalse(told.isEmpty(), whole::toString);
        UndividedByARelation.IntOperation last = told.getLast();
        assertEquals(3, last.form().coefs().size(), whole::toString);
        assertTrue(last.after().stream().map(told::get)
                .anyMatch(before -> before.form().coefs().size() == 2
                        && !before.form().coefs().keySet().toString().contains("k")),
                whole::toString);
    }

    @Test
    void aTotalOfWhatAClosureMakesOfEachElementStopsWhereAnApplicationDoes() {
        String report = report("n: Int, m: Int, k: Int", UNUSED,
                "List.sum(List.map(x -> 2 * x, [n, m])) >= k");
        assertTrue(whereEveryRunStops(report).startsWith("every run stops in 2 * n where"),
                report);
        assertTrue(whereEveryRunStops(report).contains("in 2 * m where"), report);
    }

    /**
     * A value looked up under a key and handed to a closure gets through the closure only where
     * what the closure works out is told: {@code v + 1 - 1} answers {@code v} and stops at the
     * greatest {@code Int}, and its sum is worked out where the entry is held, so the lines are
     * drawn on the sum as written ({@code v >= q} is on {@code q}, not on {@code q - 1}). A
     * closure whose stop nothing tells is not taken to get through.
     */
    @Test
    void aValueLookedUpAndHandedToAClosureIsTakenToGetThroughOnlyWhatIsTold() {
        String inputs = "k: String, m: Map<String, Int>, q: Int";
        String told = report(inputs, UNUSED,
                "(Map.get(k, m) |> Option.map(v -> v + 1 - 1) |> Option.withDefault(0)) >= q");
        assertEquals(Set.of("m[*]"), related(told), told);
        assertEquals(Set.of(), notShown(told), told);
        String untold = report(inputs, UNUSED,
                "(Map.get(k, m) |> Option.map(v -> Int.abs(v)) |> Option.withDefault(0)) >= q");
        assertEquals(Set.of(), related(untold), untold);
        assertEquals(Set.of("m[*]", "q"), notShown(untold), untold);
    }

    /**
     * A total read off a name is read off what the name was given, and so is what working that
     * out does: {@code n.value + 1 - 1} totals what {@code n.value} does, and stops at the
     * greatest {@code Int}, whether the list it makes or the total is what the name holds.
     */
    @Test
    void aTotalReadThroughANameIsAskedOfWhatTheNameWasGiven() {
        String inputs = "gross: Int, ns: List<Nat>";
        String theTotal = report(inputs, NAT, """
                {
                    let s = List.sum(List.map(n -> n.value + 1 - 1, ns))
                    gross >= s
                }""");
        assertEquals(Set.of(), related(theTotal), theTotal);
        String theList = report(inputs, NAT, """
                {
                    let xs = List.map(n -> n.value + 1 - 1, ns)
                    gross >= List.sum(xs)
                }""");
        assertEquals(Set.of(), related(theList), theList);
        assertEquals(Set.of("List.sum(ns[*])", "gross"), notShown(theList), theList);
    }

    /**
     * A name between the total and the list a closure made is no evidence of its own: what the
     * name was given is worked out, and so is what each name read in that reads. Ordered the
     * other way round through a name or not, a total of {@code x + 1 - 1} over the elements stops
     * at the greatest {@code Int}, and the comparison is not taken to tell every operation.
     */
    @Test
    void aNameBetweenTheTotalAndWhatAClosureMadeShowsNothingOfTheClosure() {
        String inputs = "gross: Int, ns: List<Nat>";
        for (String body : List.of("""
                {
                    let ys = List.map(n -> n.value + 1 - 1, ns)
                    let rev = List.reverse(ys)
                    gross >= List.sum(rev)
                }""", """
                {
                    let ys = List.map(n -> n.value + 1 - 1, ns)
                    gross >= List.sum(List.reverse(ys))
                }""", """
                gross >= List.sum(List.reverse(List.map(n -> n.value + 1 - 1, ns)))""")) {
            String report = report(inputs, NAT, body);
            assertEquals(Set.of(), related(report), report);
        }
    }

    /**
     * What a run works out to reach a value read through a name is worked out where the name was
     * given it, and a row of the comparison gets past it all the same: {@code n + 1 - 1} in a list
     * bound to a name stops at the greatest {@code Int}, whether the total reads the name or a
     * name for the list ordered the other way round. Written at the total, its sum is told.
     */
    @Test
    void whatANameWasGivenIsWorkedOutBeforeTheRowGetsToTheTotal() {
        String inputs = "n: Int, m: Int, k: Int";
        for (String condition : List.of("""
                {
                    let ys = [n + 1 - 1, m]
                    List.sum(ys) >= k
                }""", """
                {
                    let ys = [n + 1 - 1, m]
                    let rev = List.reverse(ys)
                    List.sum(rev) >= k
                }""")) {
            UndividedByARelation.Working read = workingOf(inputs, condition);
            assertEquals(WhatARelationLeavesUndivided.Told.SOME, read.told(), read::toString);
        }
        UndividedByARelation.Working written = workingOf(inputs, "List.sum([n + 1 - 1, m]) >= k");
        assertEquals(WhatARelationLeavesUndivided.Told.EVERY, written.told(), written::toString);
    }

    /**
     * The year of a date moved by a count written down is a number defined only where the move
     * leaves a date, as the shift it is taken through keeps it, so the move gets there
     * wherever the number has a value, read through a name or not; the count, folded, is worked
     * out on every run. Moved by {@code n + 1 - 1} the date is no such number, and the sum stops
     * at the greatest {@code Int} whatever year it would have come to.
     */
    @Test
    void aNumberReadThroughANameStandsOnlyWhereTheLibraryWorkedItOut() {
        String inputs = "b: Date, n: Int, k: Int";
        UndividedByARelation.Working byASum = workingOf(inputs, """
                {
                    let moved = Date.addDays(n + 1 - 1, b)
                    Date.year(moved) >= k
                }""");
        assertEquals(WhatARelationLeavesUndivided.Told.SOME, byASum.told(), byASum::toString);
        UndividedByARelation.Working byAWrittenCount = workingOf(inputs, """
                {
                    let moved = Date.addDays(0 - 1, b)
                    Date.year(moved) >= k
                }""");
        assertEquals(WhatARelationLeavesUndivided.Told.EVERY, byAWrittenCount.told(),
                byAWrittenCount::toString);
    }

    /** The left side of the comparison {@code condition} of a behavior taking {@code inputs},
     *  where it is read, as what a run works out to reach it. */
    private static boolean theLeftSideGetsThereWhereItsAnswerHasAPlace(String inputs,
                                                                       String condition) {
        ReadComparisons read = ReadComparisons.ofTheAnalysis("""
                module w1
                data Unused = Int
                behavior m : (%s) -> Bool
                let m (%s) = %s
                """.formatted(inputs, inputs.replaceAll(": [A-Za-z<>]+", ""), condition), "m");
        ComparisonReadings.Reading only = read.only();
        StatedComparison stated =
                ((ComparisonReadings.Stated.AComparison) only.statement()).comparison();
        return WorkedOutToReachIt.of(read.inputs().reading(read.rules()))
                .endsOnlyWhereItsAnswerHasNoPlace(new Denotation(stated.left(), only.reads()));
    }

    /**
     * That a total has a place says nothing of a part of it: the total of {@code 2 * n} and
     * {@code -n} is {@code n}, which has a place where {@code 2 * n} does not, and the length of a
     * list of {@code 2 * n} is one wherever doubling stops. Only the answer a row stands at is
     * answered for by where it stands. An operator over numbers written down is worked out where it
     * is folded, past the type or not.
     */
    @Test
    void thatTheWholeHasAPlaceSaysNothingOfAPart() {
        String inputs = "n: Int, m: Int, k: Int";
        assertFalse(theLeftSideGetsThereWhereItsAnswerHasAPlace(inputs,
                "List.sum([Int.multiply(n, 2), Int.multiply(n, -1)]) >= k"));
        assertFalse(theLeftSideGetsThereWhereItsAnswerHasAPlace(inputs,
                "List.length(List.reverse([Int.multiply(n, 2)])) >= k"));
        assertTrue(theLeftSideGetsThereWhereItsAnswerHasAPlace(inputs, "List.sum([n, m]) >= k"));
        assertTrue(theLeftSideGetsThereWhereItsAnswerHasAPlace(inputs,
                "List.sum([n, 0 - 1]) >= k"));
        assertFalse(theLeftSideGetsThereWhereItsAnswerHasAPlace(inputs,
                "List.sum([n, " + MAX + " + 1]) >= k"));
        for (String condition : List.of(
                "List.sum([Int.multiply(n, 2), Int.multiply(n, -1)]) >= k",
                "List.length(List.reverse([Int.multiply(n, 2)])) >= k")) {
            UndividedByARelation.Working read = workingOf(inputs, condition);
            assertFalse(read.told() == WhatARelationLeavesUndivided.Told.EVERY
                            && read.operations().isEmpty(), read::toString);
            assertFalse(read.told() == WhatARelationLeavesUndivided.Told.NOTHING_SAID,
                    read::toString);
        }
    }

    private static final String DISCARDED = "{ let discarded = " + MAX + " + 1\n 1 }";

    /** What the rule that reads the comparison {@code condition} over {@code n} and {@code k}
     *  says its rows work out, where it says more than the arithmetic. */
    private static UndividedByARelation.Working whatTheRuleWorksOut(String inputs,
                                                                    String condition) {
        ReadComparisons read = ReadComparisons.ofTheAnalysis("""
                module w1
                data Unused = Int
                behavior m : (%s) -> Bool
                let m (%s) = %s
                """.formatted(inputs, inputs.replaceAll(": [A-Za-z<>]+", ""), condition), "m");
        ComparisonReadings.Reading only = read.only();
        return Pullback.ofAComparisonOnTheInput(
                ((ComparisonReadings.Stated.AComparison) only.statement()).comparison(),
                only.reads(), read.inputs().reading(read.rules())).working().get();
    }

    /** Whether no row of {@code working} is shown to get past what it works out: not every
     *  operation is told, or one told is a number past the type on every run. */
    private static boolean noRowIsShownToGetPast(UndividedByARelation.Working working) {
        return working.told() == WhatARelationLeavesUndivided.Told.SOME
                || working.operations().stream().anyMatch(operation ->
                        operation.form().coefs().isEmpty()
                                && (operation.form().constant().compareTo(
                                        ExactRatio.of(operation.greatest())) > 0
                                || operation.form().constant().compareTo(
                                        ExactRatio.of(operation.least())) < 0));
    }

    /**
     * That a value folds to a number says what the number is, and nothing of what working it out
     * runs: a fold follows a name and a {@code let} to the value they stand as, and a value bound
     * on the way and never read is worked out all the same. Inside an operand, behind a name,
     * on the side a rule takes by the number it folds to, or as the mode a rounding is handed, an
     * initializer past the type stops every run, and no row is shown to get past it.
     */
    @Test
    void thatAValueFoldsToANumberSaysNothingOfWorkingItOut() {
        String inputs = "n: Int, k: Int";
        assertFalse(theLeftSideGetsThereWhereItsAnswerHasAPlace(inputs,
                "List.sum([1 + (" + DISCARDED + ")]) >= k"));
        assertTrue(theLeftSideGetsThereWhereItsAnswerHasAPlace(inputs,
                "List.sum([1 + ({ let kept = 1\n kept })]) >= k"));
        UndividedByARelation.Working behindAName = workingOf(inputs, """
                {
                    let x = %s
                    n + x >= k
                }""".formatted(DISCARDED));
        assertTrue(noRowIsShownToGetPast(behindAName), behindAName::toString);
        UndividedByARelation.Working aDateBehindAName = workingOf("b: Date, k: Int", """
                {
                    let moved = { let discarded = %s + 1
                        Date.addDays(-1, b) }
                    Date.year(moved) >= k
                }""".formatted(MAX));
        assertTrue(noRowIsShownToGetPast(aDateBehindAName), aDateBehindAName::toString);
        UndividedByARelation.Working aWrittenDateBehindAName = workingOf("b: Date, k: Int", """
                {
                    let start = { let discarded = %s + 1
                        Date("2020-01-01") }
                    b >= start
                }""".formatted(MAX));
        assertTrue(noRowIsShownToGetPast(aWrittenDateBehindAName),
                aWrittenDateBehindAName::toString);
        for (String condition : List.of(
                "Date.year(Date.addDays(n, Date(\"2020-01-01\"))) >= (" + DISCARDED + ")",
                "Rational.toInt(DOWN, n / 2) >= (" + DISCARDED + ")",
                "Rational.toInt({ let discarded = " + MAX + " + 1\n DOWN }, n / 2) >= 3")) {
            UndividedByARelation.Working restated = whatTheRuleWorksOut(inputs, condition);
            assertTrue(noRowIsShownToGetPast(restated), () -> condition + " " + restated);
        }
        for (String condition : List.of(
                "Date.year(Date.addDays(n, Date(\"2020-01-01\"))) >= 2027",
                "Rational.toInt(DOWN, n / 2) >= 3")) {
            UndividedByARelation.Working restated = whatTheRuleWorksOut(inputs, condition);
            assertEquals(WhatARelationLeavesUndivided.Told.EVERY, restated.told(),
                    () -> condition + " " + restated);
        }
    }

    /**
     * How many a list holds is no number a closure applied to its elements adds into, so that
     * closure is not between nought and it: {@code List.length(List.map(x -> 2 * x, ns))} stops
     * at a doubling past the type with the length one. Nor is a count a walk keeps, whose step
     * adds one and not the element it is handed. Neither comparison is taken to tell every
     * operation its rows get past, where how many there are alone tells them all.
     */
    @Test
    void aCountOfWhatAClosureMadeIsNotAnswerForTheClosure() {
        String inputs = "ns: List<Int>, k: Int";
        UndividedByARelation.Working counted = workingOf(inputs,
                "List.length(List.map(x -> 2 * x, ns)) >= k");
        assertEquals(WhatARelationLeavesUndivided.Told.SOME, counted.told(), counted::toString);
        UndividedByARelation.Working walked = workingOf(inputs,
                "List.fold((acc, x) -> acc + 1, 0, List.map(y -> 2 * y, ns)) >= k");
        assertEquals(WhatARelationLeavesUndivided.Told.SOME, walked.told(), walked::toString);
        UndividedByARelation.Working alone = workingOf(inputs, "List.length(ns) >= k");
        assertEquals(WhatARelationLeavesUndivided.Told.EVERY, alone.told(), alone::toString);
    }

    /**
     * Nor is a total of what a list is ordered into answer for the key it was ordered by: every
     * key is worked out, and {@code 2 * n.value} passes the type where the total of
     * {@code n.value} does not. Ordered by what is added, the same total is left.
     */
    @Test
    void aTotalOfWhatWasOrderedIsNotAnswerForTheKeyItWasOrderedBy() {
        String inputs = "gross: Int, ns: List<Nat>";
        String byTwice = report(inputs, NAT,
                "gross >= List.sum(List.map(n -> n.value, List.sortBy(n -> 2 * n.value, ns)))");
        assertEquals(Set.of(), related(byTwice), byTwice);
        String added = report(inputs, NAT,
                "gross >= List.sum(List.map(n -> 2 * n.value, ns))");
        assertTrue(related(added).contains("List.sum({2·the element itself + 0 | ns[*]})"),
                added);
    }

    /** A walk over {@code outer} copies of {@code n} whose step adds what doubling each of
     *  {@code inner} copies of it comes to. */
    private static String aWalkOverWhatAClosureMakes(int outer, int inner) {
        return "List.fold((acc, x) -> acc + List.sum(List.map(y -> 2 * y, ["
                + String.join(", ", Collections.nCopies(inner, "n")) + "])) + x, 0, ["
                + String.join(", ", Collections.nCopies(outer, "n")) + "]) >= k";
    }

    /**
     * Reading a walk or a total element by element makes a reading of each element, and a walk
     * whose step reads another so makes that many again for each of its own: they are counted
     * together for the comparison, readings tried and kept apart included. Ten of ten is read so
     * and every operation told; thirty of thirty is more than are made, and the comparison is not
     * taken to tell every operation, rather than read a square of them.
     */
    @Test
    void readingsElementByElementAreCountedTogetherForTheComparison() {
        UndividedByARelation.Working few = workingOf("n: Int, k: Int",
                aWalkOverWhatAClosureMakes(10, 10));
        assertEquals(WhatARelationLeavesUndivided.Told.EVERY, few.told(), few::toString);
        UndividedByARelation.Working many = workingOf("n: Int, k: Int",
                aWalkOverWhatAClosureMakes(30, 30));
        assertEquals(WhatARelationLeavesUndivided.Told.SOME, many.told(), many::toString);
    }

    /** An empty list is handed to no application, so the closure owes nothing. */
    @Test
    void aClosureAppliedToNothingStopsNoRun() {
        String report = report("k: Int", UNUSED,
                "List.sum(List.map(x -> 2 * x + " + MAX + ", [])) >= k");
        assertEquals("", whereEveryRunStops(report), report);
    }

    /**
     * Each element held at nought or more and only added and multiplied by a written number of at
     * least one, every number worked out on the way to the total lies between nought and the
     * total: a run gets through wherever the total is an {@code Int}, and the total is left either
     * way. The same over numbers that may be below nought, or taken away from, is not shown:
     * {@code n.value + 1 - 1} totals what {@code n.value} does, and stops at the greatest
     * {@code Int} where that total does not. Nor is a function handed by its name, whose body is
     * in no tree read here.
     */
    @Test
    void aTotalOfWhatIsNeverBelowNoughtGetsThroughWhereverTheTotalIsAnInt() {
        String inputs = "gross: Int, ns: List<Nat>";
        assertTrue(related(report(inputs, NAT,
                "gross >= List.sum(List.map(n -> 2 * n.value, ns))"))
                .contains("List.sum({2·the element itself + 0 | ns[*]})"));
        assertEquals(Set.of("List.sum({1·the element itself + -1 | ns[*]})", "gross"),
                notShown(report(inputs, NAT,
                        "gross >= List.sum(List.map(n -> n.value - 1, ns))")));
        String byAName = report(inputs, NAT + "\nlet lessOne (n: Nat) : Int = n.value + 1 - 1",
                "gross >= List.sum(List.map(lessOne, ns))");
        assertEquals(Set.of(), related(byAName), byAName);
        String backAgain = report(inputs, NAT,
                "gross >= List.sum(List.map(n -> n.value + 1 - 1, ns))");
        assertEquals(Set.of(), related(backAgain), backAgain);
        assertEquals(Set.of("List.sum({2·the element itself + 0 | ns[*]})", "gross"),
                notShown(report("gross: Int, ns: List<Int>", UNUSED,
                        "gross >= List.sum(List.map(n -> 2 * n, ns))")));
    }

    /**
     * A walk from nought adding numbers held at nought or more is never past its total, so it gets
     * through wherever the total is an {@code Int}. From below nought, or over numbers that may
     * be below it, an answer on the way can pass the type where the total does not.
     */
    @Test
    void aWalkAddingWhatIsNeverBelowNoughtGetsThroughWhereverItsAnswerIsAnInt() {
        String inputs = "gross: Int, ns: List<Nat>";
        String fromNought = report(inputs, NAT,
                "gross >= List.fold((acc, n) -> acc + n.value, 0, ns)");
        assertTrue(related(fromNought).contains("List.sum(ns[*])"), fromNought);
        String belowNought = report(inputs, NAT,
                "gross >= List.fold((acc, n) -> acc + n.value, -5, ns)");
        assertEquals(Set.of("List.sum(ns[*])", "gross"), notShown(belowNought), belowNought);
        String ofInts = report("gross: Int, ns: List<Int>", UNUSED,
                "gross >= List.fold((acc, n) -> acc + n, 0, ns)");
        assertEquals(Set.of("List.sum(ns)", "gross"), notShown(ofInts), ofInts);
        assertFalse(ofInts.contains("every run stops"), ofInts);
    }
}
