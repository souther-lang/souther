package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.diag.SourceRendering;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.OfferingRequest;
import souther.compiler.report.GeneratedRows;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A value singled out beside a line on the same position is a class of its own, and the run it
 * falls in is a class without it.
 *
 * <p>The lines and the values singled out are distinctions on one order, so the classes are what
 * all of them leave together. The run is not cut at the value: below ten, the values either side of
 * three are ones the model treats alike, and a class for each would ask the rows for a distinction
 * no rule makes.
 */
class AValueSingledOutBesideALineIsAClassOfItsOwnTest {

    @Test
    void theValueTheRunWithoutItAndTheRunPastTheLineAreTheClasses() {
        assertEquals(List.of("= 3", "x < 10 and x /= 3", "10 <= x"),
                labels(classesOf("x == 3 || x >= 10")));
    }

    /**
     * A value at the end a run keeps moves the end past it, which is how the rest is said — and
     * the ends the rest gives as one run are the same ones its name says.
     */
    @Test
    void aValueAtTheEndOfARunLeavesTheRunPastIt() {
        List<PartitionClass> classes = classesOf("x == 10 || x >= 10");
        assertEquals(List.of("x < 10", "= 10", "10 < x"), labels(classes));
        NumericDomain.Bounds ends = classes.get(2).recognises().numbers().asOneRun();
        assertNotNull(ends, "a run less the value at its end is a run");
        assertTrue(ends.min() != null && !ends.min().inclusive()
                && ends.min().at().sameAs(Count.of(10)) && ends.max() == null, ends::toString);
    }

    @Test
    void everyValueSingledOutOfOneRunIsTakenOutOfIt() {
        assertEquals(List.of("= 3", "= 5", "x < 10 and x /= 3, 5", "10 <= x"),
                labels(classesOf("x == 3 || x == 5 || x >= 10")));
    }

    /**
     * A run the value leaves nothing of is the value alone, and no class beside it.
     *
     * <p>Below one and from nought up is nought, on the whole numbers. A class holding nothing
     * there would be one no row is ever counted at.
     */
    @Test
    void aRunThatIsTheValueAloneLeavesNoRestBesideIt() {
        assertEquals(List.of("= 0", "1 <= x"),
                labels(classesIn("""
                        module probe

                        data Low
                        data High

                        data Tally = Int
                            invariant nonNegative = value >= 0

                        behavior pick : (t: Tally) -> Low | High
                        let pick (t) = if t.value == 0 || t.value >= 1 then High else Low
                        """)));
    }

    /**
     * The rest of the run stands at a value it holds, which is never the one taken out.
     *
     * <p>Nine is where a value is looked for in the run below ten, so the run without nine is the
     * one where a search that stepped onto the hole would offer it.
     */
    @Test
    void theRestOfTheRunIsRepresentedAwayFromTheValue() {
        PartitionClass rest = classesOf("x == 9 || x >= 10").get(1);
        assertEquals("x < 10 and x /= 9", rest.label());
        RepresentativeSource.Values written =
                assertInstanceOf(RepresentativeSource.Values.class, rest.representatives());
        assertFalse(written.written().isEmpty(), "the rest of the run has a value written for it");
        for (FixtureTemplate each : written.written()) {
            long at = Long.parseLong(each.text());
            assertTrue(at != 9 && rest.holdsTheNumberAt(Count.of(at)),
                    each.text() + " is not a value of " + rest.label());
        }
    }

    /** What a search for the rest of the run walks is the run without the value. */
    @Test
    void theNumbersTheRestAsksForAreTheRunWithoutTheValue() {
        PartitionClass rest = classesOf("x == 3 || x >= 10").get(1);
        Recognition.OfACount count =
                assertInstanceOf(Recognition.OfACount.class, rest.recognises());
        Carrier on = count.orders().answered();
        LevelRegion asked = NumbersAskedFor.ofTheClass(count.is(), on).values();
        assertFalse(asked.contains(new Level.OnACarrier(on, Count.of(3))), asked.toString());
        assertTrue(asked.contains(new Level.OnACarrier(on, Count.of(2))), asked.toString());
        assertTrue(asked.contains(new Level.OnACarrier(on, Count.of(4))), asked.toString());
        assertFalse(asked.contains(new Level.OnACarrier(on, Count.of(10))), asked.toString());
    }

    /**
     * Beside a row at the value, rows are composed for the run around it and for the run past the
     * line — and the one around it is not at the value.
     */
    @Test
    void aRowIsComposedForTheRunAroundTheValue() {
        String block = generatedFor("""
                module probe

                data Low
                data High

                behavior pick : (x: Int) -> Low | High
                let pick (x) = if x == 3 || x >= 10 then High else Low

                example pick
                    | "at three" : (3) -> High
                """);
        assertTrue(block.contains("fills x=x < 10 and x /= 3"), block);
        List<Long> offered = offeredAt(block);
        assertTrue(offered.stream().anyMatch(at -> at < 10 && at != 3), block);
        assertTrue(offered.stream().anyMatch(at -> at >= 10), block);
        assertFalse(offered.contains(3L), block);
    }

    /** A row of an example block, with the number it is written at. */
    private static final Pattern ROW = Pattern.compile("\\s*\\|.*\\((-?\\d+)\\)\\s*->.*");

    /** The numbers the rows {@code block} offers are written at. */
    private static List<Long> offeredAt(String block) {
        List<Long> out = new ArrayList<>();
        for (String line : block.lines().toList()) {
            Matcher row = ROW.matcher(line);
            if (row.matches()) {
                out.add(Long.parseLong(row.group(1)));
            }
        }
        return out;
    }

    private static List<String> labels(List<PartitionClass> classes) {
        return classes.stream().map(PartitionClass::label).toList();
    }

    /** The classes of {@code x} under {@code guard}. */
    private static List<PartitionClass> classesOf(String guard) {
        return classesIn("""
                module probe

                data Low
                data High

                behavior pick : (x: Int) -> Low | High
                let pick (x) = if %s then High else Low
                """.formatted(guard));
    }

    /** The classes of the one measure of {@code pick} in {@code source}. */
    private static List<PartitionClass> classesIn(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        List<Axis> axes =
                compilation.db().ask(new Adequacy.Divided("probe", "pick")).value().axes();
        assertNotNull(axes, () -> "the model compiles: " + compilation.errors());
        assertEquals(1, axes.size(), () -> "one measure: " + axes);
        return axes.getFirst().classes();
    }

    private static String generatedFor(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, Adequacy.Filling> all =
                Adequacy.generatedOf(compilation.db(), compilation.modules().get(0));
        assertNotNull(all, "the model under test compiles");
        return GeneratedRows.of(Adequacy.offeredFor(compilation.db(),
                        OfferingRequest.overTheModule("probe")),
                Map.of(), SourceRendering.namedByIdentity(compilation.texts()),
                compilation.db()).text();
    }
}
