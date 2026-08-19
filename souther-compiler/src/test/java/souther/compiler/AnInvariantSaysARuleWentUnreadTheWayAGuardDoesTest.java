package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceNameResolver;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The same rule, written as an {@code invariant} and as a {@code guard}, reported the same way.
 *
 * <p>ADR-0090's promise: a rule this could not read is named, whichever rule it was. The two
 * behaviors below compare the same arithmetic form over two positions — one in a declaration, one
 * in a body — and a reader is owed the same sentence about both.
 *
 * <p>Issue #868. The {@code invariant}'s half was silent, and what silenced it was that its fields
 * carry a bound of their own: the account was kept as what a position was left with if nothing
 * divided it, so a line read from one rule answered for the rule beside it. A reader was left with
 * a model whose only stated rule about {@code length} looked like the one on {@code Cm}.
 */
class AnInvariantSaysARuleWentUnreadTheWayAGuardDoesTest {

    private static final String MODEL = """
            module example.parcels

            data Cm = Int
                invariant value >= 0

            data Parcel = { length: Cm, width: Cm }
                invariant Int.add(length.value, width.value) <= 150

            data Order = { straw: Cm, choco: Cm }

            data Ok
            data No

            behavior quote : (parcel: Parcel) -> Ok | No
                constructs Ok
            let quote (parcel) = Ok

            behavior mix : (order: Order) -> Ok | No
                constructs Ok, No
            let mix (order) =
                if Int.add(order.straw.value, order.choco.value) <= 150 then Ok else No
            """;

    private static String blockOf(String behavior) {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        String human = AdequacyReport.of(compilation).human(SourceNameResolver.identity());
        StringBuilder block = new StringBuilder();
        boolean inside = false;
        for (String line : human.split("\n", -1)) {
            if (line.startsWith("  ") && !line.startsWith("   ")) {
                inside = line.startsWith("  " + behavior + " ");
            }
            if (inside) {
                block.append(line).append('\n');
            }
        }
        return block.toString();
    }

    /** The {@code guard}, which always said it, at both the positions it compares. */
    @Test
    void aGuardNamesBothPositionsItCompares() {
        String block = blockOf("mix");

        assertTrue(block.contains("not read: order.straw"), block);
        assertTrue(block.contains("not read: order.choco"), block);
    }

    /** And the {@code invariant} of the same shape, at both the positions it compares. */
    @Test
    void andSoDoesAnInvariantOfTheSameShape() {
        String block = blockOf("quote");

        assertTrue(block.contains("not read: parcel.length"), block);
        assertTrue(block.contains("not read: parcel.width"), block);
    }

    /** In the same words, since what stopped each of them is the same fact about this compiler. */
    @Test
    void andInTheSameWords() {
        assertEquals(saidAbout(blockOf("mix"), "order.straw"),
                saidAbout(blockOf("quote"), "parcel.length"));
    }

    /**
     * And the line the fields' own type draws is still drawn.
     *
     * <p>The rule beside it went unread; this one did not. A reading that answered the pair with
     * one verdict would have taken the boundary with it.
     */
    @Test
    void andTheBoundTheFieldsOwnTypeStatesIsStillALine() {
        String block = blockOf("quote");

        assertTrue(block.contains("boundary    0/0   (2 not measured"), block);
    }

    /** One clause and one sentence: what a reader has to lift is one thing. */
    @Test
    void andOnceEach() {
        String block = blockOf("quote");

        assertEquals(1, block.lines().filter(line -> line.contains("not read: parcel.length")).count(),
                block);
    }

    /**
     * And one clause is one sentence, whichever reading of it gave up first.
     *
     * <p>A rule about a position no line can be drawn on is a rule the end reading refuses for one
     * cause and the value reading for another. Read off both, the report printed two lines about
     * one clause naming two different limits — a reader cannot act on that, and only one of them is
     * what would give the position an axis.
     */
    @Test
    void andOnceWhereTwoReadingsBothGaveUpOnTheSameClause() {
        Compilation compilation = Compilation.ofSource("""
                module example.stages

                data Prospecting
                data Qualified
                data Won
                data Stage = Prospecting | Qualified | Won

                data AtLeastQualified = Qualified
                    invariant value >= Prospecting

                data Ok

                behavior stage : (q: AtLeastQualified) -> Ok
                    constructs Ok
                let stage (q) = Ok
                """, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        String human = AdequacyReport.of(compilation).human(SourceNameResolver.identity());

        assertEquals(1, human.lines().filter(line -> line.contains("not read: q ")).count(), human);
        assertTrue(human.contains("no line can be drawn on"), human);
    }

    private static String saidAbout(String block, String position) {
        return block.lines().filter(line -> line.contains("not read: " + position + " "))
                .map(line -> line.substring(line.indexOf('(')))
                .findFirst().orElseThrow(() -> new AssertionError(
                        "nothing said about `" + position + "`: " + block));
    }
}
