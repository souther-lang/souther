package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * What a row away from a border's line is owed for, said where the region was worked out.
 *
 * <p>A row at the line is owed for the line, and the line is the same wherever it is read. A row
 * away from it is owed for the line and for whatever stops the region on the far side — so two
 * readings of one line can be owed different rows there, and what tells them apart is that far end.
 *
 * <p>Said by the border rather than read back off what it came to. Which of the two kinds of region
 * a point is, and what stopped it, are settled in the branch that builds the demand; a reader that
 * took a criterion over everything-but-one value and called it the second kind would be answering
 * from the shape of the demand rather than from the rule that drew the line.
 */
class WhatARowAwayFromALineIsOwedForTest {

    /** One clause, read at a behavior that cuts the same number and at one that does not. */
    private static final String AMOUNT = """
            module example.owed

            data Amount = Int
                invariant value >= 0

            data Small
            data Large
            data Size = Small | Large
            data Ok

            behavior guarded : (a: Amount) -> Size
            let guarded (a) = if a.value <= 100 then Small else Large

            behavior bare : (a: Amount) -> Ok
            let bare (a) = Ok

            example guarded
                | "x" : (Amount(1)) -> Small

            example bare
                | "y" : (Amount(1)) -> Ok
            """;

    /** A clause stopping a length, where the run below it reaches an end no clause wrote. */
    private static final String LENGTH = """
            module example.extent

            data Name = String
                invariant String.length(value) <= 9

            data Ok

            behavior take : (n: Name) -> Ok
            let take (n) = Ok

            example take
                | "x" : (Name("abc")) -> Ok
            """;

    /** A rule that names one value rather than a side of it. */
    private static final String SINGLED = """
            module example.singled

            data Code = Int
            data Yes
            data No
            data Answer = Yes | No

            behavior check : (c: Code) -> Answer
            let check (c) = if c.value == 5 then Yes else No

            example check
                | "x" : (Code(1)) -> No
            """;

    /**
     * A run that stops at another rule's line is owed to that rule.
     *
     * <p>{@code guarded} compares against a hundred, so the run above {@code Amount}'s floor stops
     * there. A row inside it answers for the floor and for the comparison at once, and the second is
     * what a reading of the same clause somewhere else does not have.
     */
    @Test
    void aRunStoppingAtALineIsOwedToThatLine() {
        RegionBasis basis = onlyBasis(AMOUNT, "example.owed", "guarded", "a = 0", PointRole.IN);

        FarEnd end = ((RegionBasis.Beside) basis).farEnd();
        assertInstanceOf(FarEnd.AtALine.class, end, "the run stops at a line somebody wrote");
        assertEquals("100", ((FarEnd.AtALine) end).where().at().written().key(),
                "which is the comparison's, at a hundred");
    }

    /** And where nothing stops it, the run is owed to the line and to the order's own end. */
    @Test
    void aRunNothingStopsIsOwedToTheEndOfTheOrder() {
        RegionBasis basis = onlyBasis(AMOUNT, "example.owed", "bare", "a = 0", PointRole.IN);

        assertEquals(new RegionBasis.Beside(new FarEnd.AtTheOrderEnd(
                        souther.compiler.numeric.Towards.ABOVE)), basis,
                "an Int runs on, and no rule says where it stops");
    }

    /**
     * A run stopping where the rules leave the quantity is owed to that end and to no line.
     *
     * <p>A length is never negative and no clause of the model says so, so there is nobody to name
     * for the end the run stops at below.
     */
    @Test
    void aRunStoppingWhereTheRulesLeaveOffIsOwedToNoLine() {
        RegionBasis basis =
                onlyBasis(LENGTH, "example.extent", "take", "String.length(n) = 9", PointRole.IN);

        assertInstanceOf(FarEnd.AtTheDomain.class, ((RegionBasis.Beside) basis).farEnd(),
                "the run stops where every rule leaves the quantity together");
    }

    /**
     * What a rule that names a value leaves is not a run and is owed for the line alone.
     *
     * <p>{@code c.value == 5} puts every other value in one class. That class is two runs with the
     * named value between them, so there is no far end to be owed to — and which value is left out
     * is the line's, which a debt is keyed on already.
     */
    @Test
    void whatARuleNamingAValueLeavesIsOwedForTheLineAlone() {
        assertEquals(RegionBasis.THE_REST,
                onlyBasis(SINGLED, "example.singled", "check", "c = 5", PointRole.OUT),
                "everything but the value the rule names, and nothing beside it");
    }

    /** The one thing a row at that point is owed for, refusing where there is more than one. */
    private static RegionBasis onlyBasis(String model, String module, String behavior, String label,
                                         PointRole role) {
        PointAnswer answer = borderAt(model, module, behavior, label).border().answer(role);
        assertInstanceOf(PointAnswer.InRegion.class, answer,
                () -> "the " + role + " point of " + label + " is a region");
        List<RegionBasis> bases = answer.bases();
        assertEquals(1, bases.size(), () -> "one thing stops this run: " + bases);
        return bases.get(0);
    }

    private static BorderAssessment borderAt(String model, String module, String behavior,
                                             String label) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, List<BorderAssessment>> boundaries =
                Adequacy.boundariesOf(compilation.db(), module);
        assertNotNull(boundaries, "the model under test compiles");
        List<BorderAssessment> lines = boundaries.get(behavior);
        assertNotNull(lines, () -> behavior + " draws lines: " + boundaries.keySet());
        return lines.stream().filter(each -> each.label().equals(label)).findFirst()
                .orElseThrow(() -> new AssertionError(label + " is not a line of " + behavior + ": "
                        + lines.stream().map(BorderAssessment::label).toList()));
    }
}
