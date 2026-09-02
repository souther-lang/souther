package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.inputs.BlockReason;
import souther.compiler.query.Compilation;
import souther.compiler.query.Scopes;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A comparison the arithmetic read is filed at the quantity it cuts, and nowhere else.
 *
 * <p>What a rule is about is the quantity its canonical form comes to, so a position that cancelled
 * out of that form is one the rule says nothing about. Filed at the positions the comparison
 * mentions instead, {@code x + y - y <= 10 * 2} left a finding at {@code y} — and the word left
 * there was the one worked out for {@code x}, which is a fact about a carrier {@code y} does not
 * have to share.
 *
 * <p>Both halves are asserted. That the cancelled position is left alone is what the change is for;
 * that the surviving ones are still filed is what stops the same assertion passing over a reader
 * that files nothing at all.
 */
class ARuleIsFiledAtWhatItsQuantityIsAboutTest {

    /**
     * One position cancels, and the threshold is not a form an end is read out of.
     *
     * <p>{@code 10 * 2} rather than {@code 20} so that the reading of ends places nothing and there
     * is a finding to file: the question is where it is filed, and a rule that came to an end
     * leaves nothing anywhere.
     */
    private static final String ONE_CANCELS = """
            module demo

            data N = { x: Int, y: Int }
                invariant said = x + y - y <= 10 * 2
            """;

    /** The same with a third position, so that what survives is a relation between two of them. */
    private static final String ONE_CANCELS_OF_THREE = """
            module demo

            data N = { x: Int, y: Int, z: Int }
                invariant said = x + y - y + z <= 10 * 2
            """;

    /** A position the rule cancelled is not one the rule is about. */
    @Test
    void aCancelledPositionIsFiledAtByNothing() {
        FieldDomains read = read(ONE_CANCELS);

        assertEquals(List.of(new BlockReason.UnreadComparisonForm()), reasonsAt(read, "x"),
                "the position the quantity is over carries what the reading was left with");
        assertEquals(List.of(), reasonsAt(read, "y"),
                "and the position it cancelled is one the rule states nothing about");
    }

    /**
     * And the surviving positions of a form over several are all of them.
     *
     * <p>The word is the one a relation between positions gets, which is what the rule that
     * survives the cancellation is. Said at {@code y} as well, an author would be sent looking for
     * a pair the rule does not name.
     */
    @Test
    void everyPositionTheQuantityRunsOverIsFiledAt() {
        FieldDomains read = read(ONE_CANCELS_OF_THREE);

        assertEquals(List.of(new BlockReason.ComparisonBetweenPositions()), reasonsAt(read, "x"));
        assertEquals(List.of(new BlockReason.ComparisonBetweenPositions()), reasonsAt(read, "z"));
        assertEquals(List.of(), reasonsAt(read, "y"));
    }

    /** Which of the places a walk met a read comparison is filed at, over every shape of quantity. */
    @Test
    void theQuantityDecidesWhichPlacesAreFiledAt() {
        List<String> met = List.of("x", "y", "z");

        assertEquals(List.of("x"),
                UnreadComparison.filedAt(new UnreadComparison.Quantity.OverOne<>("x"), met));
        assertEquals(List.of("x", "z"),
                UnreadComparison.filedAt(
                        new UnreadComparison.Quantity.OverSeveral<>(java.util.Set.of("z", "x")),
                        met),
                "in the order the walk met them, which is the order a document names them in");
        assertEquals(met,
                UnreadComparison.filedAt(new UnreadComparison.Quantity.CutsNothing<>(), met),
                "a quantity over nothing has no place of its own, and what is worth saying is that "
                        + "the model names these and cuts none of them");
    }

    /**
     * A quantity running over a place the walk never met is two readings of one comparison
     * disagreeing, and it is refused.
     *
     * <p>Which is what makes the walk the ordering and not the membership. Kept as an intersection,
     * the two would be reconciled to whatever they have in common: the rule would go out filed at
     * one place short, and nothing would say a second was ever expected.
     */
    @Test
    void aQuantityOverAPlaceTheWalkNeverMetIsRefused() {
        assertThrows(IllegalStateException.class, () -> UnreadComparison.filedAt(
                new UnreadComparison.Quantity.OverSeveral<>(java.util.Set.of("x", "z")),
                List.of("x", "y")));
        assertThrows(IllegalStateException.class, () -> UnreadComparison.filedAt(
                new UnreadComparison.Quantity.OverOne<>("z"), List.of("x", "y")));
    }

    private static List<BlockReason.RuleWithoutLineReason> reasonsAt(FieldDomains read,
                                                                     String field) {
        return read.noLineAt(RuleKey.of(field)).stream().map(FieldDomains.NoLine::why).toList();
    }

    private static FieldDomains read(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.diagnostics().values().stream()
                .flatMap(List::stream)
                .map(each -> each.diagnostic().code())
                .toList(), "the model this reads has to be one somebody could write");
        Symbols symbols = Scopes.derived(compilation.db(), "demo").value();
        TypeSymbol.AtModule name = TypeSymbols.declared(new TypeKey(symbols.module(), "N"));
        return FieldDomains.of(name,
                (Hir.Data) symbols.declaredNode(name.key()), symbols,
                souther.compiler.query.ReadAs.THE_COMPILATION_DOES);
    }
}
