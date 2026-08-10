package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the report says about a position it derived nothing at.
 *
 * <p>Two behaviors differing by three tokens. One compares a position and nothing else; the other
 * compares the same position to the same number with a second comparison in front of it. Both come
 * back with no axis, and the report used to say the same thing about both — that the model draws no
 * line there — which is true of neither, and of the second is the opposite of what the body says
 * two lines above.
 *
 * <p>So the sentence has to name which of the two happened. Not because the wording is nicer: an
 * author reading "the model draws no line here" stops looking, and the row at the line is the one
 * the model most needs.
 */
class APositionThisDidNotReadIsNotOneTheModelSaysNothingAboutTest {

    private static final String MODEL = """
            module example.repro

            data Kind = Domestic | Overseas
            data Request = { kind: Kind, cost: Int, note: String }

            data Auto
            data Manual

            behavior alone : (r: Request) -> Auto | Manual
                constructs Auto, Manual
            let alone (r) = if r.cost <= 100000 then Auto else Manual

            behavior inAConjunction : (r: Request) -> Auto | Manual
                constructs Auto, Manual
            let inAConjunction (r) =
                if r.cost >= 0 && r.cost <= 100000 then Auto else Manual

            data Deep = { note: String }
            data Middle = { deep: Deep }
            data Outer = { middle: Middle }

            behavior tooDeep : (o: Outer) -> Auto | Manual
                constructs Auto, Manual
            let tooDeep (o) = if o.middle.deep.note == "x" then Auto else Manual

            behavior byEquality : (r: Request) -> Auto | Manual
                constructs Auto, Manual
            let byEquality (r) = if r.cost == 3 then Auto else Manual

            behavior byDateTime : (at: DateTime) -> Auto | Manual
                constructs Auto, Manual
            let byDateTime (at) =
                if at < DateTime("2026-01-01T00:00:00") then Auto else Manual

            behavior nothingCompared : (r: Request) -> Auto | Manual
                constructs Auto, Manual
            let nothingCompared (r) =
                match r.kind with
                    | Domestic -> Auto
                    | Overseas -> Manual
            """;

    private static String blockOf(String behavior) {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        String human = AdequacyReport.of(compilation).human();
        StringBuilder block = new StringBuilder();
        boolean inside = false;
        for (String line : human.split("\n", -1)) {
            boolean header = line.startsWith("  ") && !line.startsWith("   ");
            if (header) {
                inside = line.startsWith("  " + behavior + " ");
            }
            if (inside) {
                block.append(line).append('\n');
            }
        }
        return block.toString();
    }

    /** A position a comparison names, in a form nothing reads. */
    @Test
    void aPositionComparedInsideAConjunctionIsSaidToBeUnread() {
        String block = blockOf("inAConjunction");

        assertTrue(block.contains("r.cost"), block);
        assertFalse(block.contains("not derivable: r.cost"),
                "the body compares it two lines above: " + block);
    }

    /** A position nothing compares, which is the sentence the other one was borrowing. */
    @Test
    void aPositionNothingComparesIsStillSaidToBeUndivided() {
        String block = blockOf("nothingCompared");

        assertTrue(block.contains("not derivable: r.cost"), block);
    }

    /**
     * A position the walk stopped short of, which is not one it looked at and found undivided.
     *
     * <p>{@code Partitions.MAX_DEPTH} is two and the generator composes to eight, so a field three
     * records down is a value a row can carry and a position nothing measured. Reported as the limit
     * it is, so that lifting the limit is work somebody can see is owed.
     */
    @Test
    void aPositionTheWalkStoppedShortOfSaysSo() {
        String block = blockOf("tooDeep");

        assertFalse(block.contains("not derivable: o.middle.deep"), block);
        assertTrue(block.contains("the walk stopped before reaching what is under it"), block);
    }

    /**
     * An equality is not a form this cannot read — it is a partition this cannot hold.
     *
     * <p>`retries == 3` divides the values the behavior distinguishes into `{3}` and everything
     * else, and the second of those is not an interval. Reported as the shape it is, because that
     * says what would have to change: a class that is not convex, rather than a reader for a form of
     * condition.
     */
    @Test
    void anEqualityIsSaidToBeAShapeRatherThanAForm() {
        String block = blockOf("byEquality");

        assertTrue(block.contains("not read: r.cost"), block);
        assertTrue(block.contains("interval"), block);
    }

    /** And a carrier no line can be drawn on is neither of those. */
    @Test
    void aCarrierNoLineIsDrawnOnSaysThat() {
        String block = blockOf("byDateTime");

        assertTrue(block.contains("not read: at"), block);
        assertFalse(block.contains("interval"), block);
    }

    /** The one that is read is not named either way. */
    @Test
    void aPositionThatWasReadIsNotNamedAtAll() {
        String block = blockOf("alone");

        assertFalse(block.contains("not derivable: r.cost"), block);
        assertFalse(block.contains("not read: r.cost"), block);
    }
}
