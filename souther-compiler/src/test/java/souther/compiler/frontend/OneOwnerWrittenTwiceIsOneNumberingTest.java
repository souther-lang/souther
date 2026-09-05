package souther.compiler.frontend;

import souther.compiler.ast.Ast;
import souther.compiler.observe.RowIdentity;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * The other half of what a reading is. What is written for one owner is numbered under one count,
 * however many places of the file wrote it; what is written for another is numbered apart.
 *
 * <p>Two blocks may be written for one behavior — {@code example}s of it, and the stand-in it is
 * given — and a reader shown the second row of {@code submit} is being shown one of that behavior's
 * rows rather than one of that block's. So the second block carries on where the first left off,
 * which is why a reading is made for an owner and handed back rather than made for each block. The
 * alternative is a number saying which block, and that is the count over the file this is all here
 * to be rid of.
 *
 * <p>And apart, because {@code example} rows and the {@code fake} beside them are two things to
 * edit. A row added to one that renumbered the other would be the file-wide count again, narrowed
 * to a behavior.
 */
class OneOwnerWrittenTwiceIsOneNumberingTest {

    private static final String MODULE = """
            module shop.orders exposing ( Amount )

            data Amount = Int
                invariant value >= 0

            behavior twice : (n: Amount) -> Amount
                constructs Amount
            let twice (n) = Amount(n.value * 2)

            behavior thrice : (n: Amount) -> Amount
                constructs Amount
            let thrice (n) = Amount(n.value * 3)
            """;

    private static final String ROWS_IN_TWO_BLOCKS = MODULE + """

            example twice
                | (Amount(1)) -> Amount(2)

            example twice
                | (Amount(2)) -> Amount(4)
            """;

    private static final String ROWS_IN_ONE_BLOCK = MODULE + """

            example twice
                | (Amount(1)) -> Amount(2)
                | (Amount(2)) -> Amount(4)
            """;

    @Test
    void aSecondBlockForOneBehaviorCarriesOnItsNumbering() {
        List<RowIdentity> acrossTwoBlocks = rowsOf(ROWS_IN_TWO_BLOCKS);
        List<RowIdentity> inOneBlock = rowsOf(ROWS_IN_ONE_BLOCK);

        assertEquals(inOneBlock, acrossTwoBlocks,
                "the rows are the same behavior's either way, so they are numbered the same way");
        assertNotEquals(acrossTwoBlocks.get(0), acrossTwoBlocks.get(1),
                "and the second block's row is not the first block's row over again");
    }

    /** And a behavior exampled after another one is numbered from its own start, the two owners
     *  being two. */
    @Test
    void andABehaviorsRowsStartWhereverItsBlockIsWritten() {
        String exampledAfterAnother = MODULE + """

                example twice
                    | (Amount(1)) -> Amount(2)

                example thrice
                    | (Amount(1)) -> Amount(3)
                """;
        String exampledAlone = MODULE + """

                example thrice
                    | (Amount(1)) -> Amount(3)
                """;

        assertEquals(rowsOf(exampledAlone), rowsOfTheLastBlock(exampledAfterAnother),
                "`thrice`'s rows are `thrice`'s, whatever was exampled before them");
    }

    private static List<RowIdentity> rowsOf(String source) {
        List<RowIdentity> identities = new ArrayList<>();
        for (Ast.Example block : CstFrontend.parse(source, null).examples()) {
            for (Ast.ExampleRow row : block.rows()) {
                identities.add(row.identity());
            }
        }
        return identities;
    }

    private static List<RowIdentity> rowsOfTheLastBlock(String source) {
        List<Ast.Example> blocks = CstFrontend.parse(source, null).examples();
        List<RowIdentity> identities = new ArrayList<>();
        for (Ast.ExampleRow row : blocks.get(blocks.size() - 1).rows()) {
            identities.add(row.identity());
        }
        return identities;
    }
}
