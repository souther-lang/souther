package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

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
                """.formatted(declarations, inputs, inputs.replaceAll(": [A-Za-z<>]+", ""), body),
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
