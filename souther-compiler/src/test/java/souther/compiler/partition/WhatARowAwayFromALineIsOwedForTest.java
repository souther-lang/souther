package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Towards;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
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
        FarEnd end = onlyBasis(AMOUNT, "example.owed", "guarded", "a = 0", PointRole.IN);

        assertInstanceOf(FarEnd.AtALine.class, end, "the run stops at a line somebody wrote");
        assertEquals("100", ((FarEnd.AtALine) end).where().at().written().key(),
                "which is the comparison's, at a hundred");
    }

    /** And where nothing stops it, the run is owed to the line and to the order's own end. */
    @Test
    void aRunNothingStopsIsOwedToTheEndOfTheOrder() {
        FarEnd basis = onlyBasis(AMOUNT, "example.owed", "bare", "a = 0", PointRole.IN);

        assertEquals(new FarEnd.AtTheOrderEnd(Towards.ABOVE), basis,
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
        FarEnd basis =
                onlyBasis(LENGTH, "example.extent", "take", "String.length(n) = 9", PointRole.IN);

        assertInstanceOf(FarEnd.AtTheDomain.class, basis,
                "the run stops where every rule leaves the quantity together");
    }

    /**
     * What a rule that names a value leaves is two runs, and each is owed for where it stops.
     *
     * <p>{@code c.value == 5} puts every other value in one class, and that class is the run under
     * the named value and the run over it with the value between them. They are two runs of the
     * arrangement like any other, so a row in one says nothing about the other and each is owed to
     * the line together with whatever stops it on the far side.
     */
    @Test
    void whatARuleNamingAValueLeavesIsTwoRunsOwedApart() {
        FarEnd below = onlyBasis(SINGLED, "example.singled", "check", "c = 5",
                new DomainPoint.InTheRegion(Towards.BELOW));
        FarEnd above = onlyBasis(SINGLED, "example.singled", "check", "c = 5",
                new DomainPoint.InTheRegion(Towards.ABOVE));

        assertNotNull(below, "the run under the value stops somewhere");
        assertNotNull(above, "and so does the run over it");
        assertNotEquals(below, above,
                "the two stop in different places, so a row in one is no row in the other");
    }

    /** Two rules of one behavior cutting at one number, with a clause's line below them. */
    private static final String TWICE_AT_ONE_PLACE = """
            module example.twice

            data Amount = Int
                invariant atLeastNothing = value >= 0

            data Small
            data Large
            data Size = Small | Large

            behavior twice : (a: Amount) -> Size
                ensures Small -> a.value <= 10
            let twice (a) = if a.value <= 10 then Small else Large

            example twice
                | "x" : (Amount(1)) -> Small
            """;

    /**
     * A run stopping where two of a body's rules drew a line is owed to each of them.
     *
     * <p>Each is enough on its own: taking either comparison away leaves the run stopping at ten.
     * So there are two rows to write there and not one — the values are the same values, and a row
     * inside answers both, but what an author is told about and what a verdict counts are the two
     * rules, since either can be moved without the other.
     */
    @Test
    void aRunTwoRulesStopIsOwedToEachOfThem() {
        PointAnswer answer = borderAt(TWICE_AT_ONE_PLACE, "example.twice", "twice", "a = 0")
                .border().answer(PointRole.IN);

        assertEquals(2, answer.bases().size(),
                () -> "two comparisons stop the run at ten: " + answer.bases());
        assertEquals(1, answer.bases().stream()
                        .map(each -> ((FarEnd.AtALine) each).where().key())
                        .distinct().count(),
                "at one place, since the values part once");
    }

    /** The one thing a row at that point is owed for, refusing where there is more than one. */
    private static FarEnd onlyBasis(String model, String module, String behavior, String label,
                                         PointRole role) {
        Border line = borderAt(model, module, behavior, label).border();
        return onlyBasis(model, module, behavior, label, line.theOne(role));
    }

    /** The same, of a point named by where it is — which is what tells two runs of one line
     *  apart. */
    private static FarEnd onlyBasis(String model, String module, String behavior, String label,
                                         DomainPoint role) {
        PointAnswer answer = borderAt(model, module, behavior, label).border().answer(role);
        assertInstanceOf(PointAnswer.InRegion.class, answer,
                () -> "the " + role + " point of " + label + " is a region");
        List<FarEnd> bases = answer.bases();
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
