package souther.compiler.check;

import souther.compiler.DefaultStdlib;
import souther.compiler.ast.Hir;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BinOp;
import souther.compiler.types.CoverageOrigin;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * An expression written with a comparing operator folds to what the relation that operator placed
 * comes to of its two sides.
 *
 * <p>The way from the operator to the answer, taken whole: what the operator placed
 * ({@link ComparisonPlacement}), the relation that placement states, and the fold of that relation
 * over two constants. Each of the six is put through it, because what is being fixed is the way and
 * not any one relation — a claim read off the wrong operator answers every question a reader can
 * ask of it, and answers them about a comparison nobody wrote.
 *
 * <p>What the relations themselves come to is fixed against how two values stand, and not here.
 */
class AComparisonFoldsToWhatItsOperatorPlacedTest {

    private static final SourcePos POS = new SourcePos(1, 1);

    /** The six as the language writes them. */
    private static final List<BinOp> COMPARING =
            List.of(BinOp.LT, BinOp.LE, BinOp.GT, BinOp.GE, BinOp.EQ, BinOp.NE);

    @Test
    void everyComparingOperatorFoldsToWhatItPlacedOverTwoConstants() {
        assertEquals(List.of(
                "1 LT 2 = true", "1 LE 2 = true", "1 GT 2 = false", "1 GE 2 = false",
                "1 EQ 2 = false", "1 NE 2 = true",
                "2 LT 2 = false", "2 LE 2 = true", "2 GT 2 = false", "2 GE 2 = true",
                "2 EQ 2 = true", "2 NE 2 = false",
                "2 LT 1 = false", "2 LE 1 = false", "2 GT 1 = true", "2 GE 1 = true",
                "2 EQ 1 = false", "2 NE 1 = true",
                // No order to answer an ordering by, and an equality all the same.
                "true LT true = not a constant", "true LE true = not a constant",
                "true GT true = not a constant", "true GE true = not a constant",
                "true EQ true = true", "true NE true = false",
                "true LT false = not a constant", "true LE false = not a constant",
                "true GT false = not a constant", "true GE false = not a constant",
                "true EQ false = false", "true NE false = true"),
                folded(List.of(
                        new Pair(new Hir.IntLit(1, POS, null), new Hir.IntLit(2, POS, null)),
                        new Pair(new Hir.IntLit(2, POS, null), new Hir.IntLit(2, POS, null)),
                        new Pair(new Hir.IntLit(2, POS, null), new Hir.IntLit(1, POS, null)),
                        new Pair(new Hir.BoolLit(true, POS, null), new Hir.BoolLit(true, POS, null)),
                        new Pair(new Hir.BoolLit(true, POS, null),
                                new Hir.BoolLit(false, POS, null)))));
    }

    /** Two written values a comparison is folded of. */
    private record Pair(Hir.Expr left, Hir.Expr right) { }

    /** Every comparing operator over every pair, as one row each. */
    private static List<String> folded(List<Pair> pairs) {
        List<String> rows = new ArrayList<>();
        for (Pair pair : pairs) {
            for (BinOp op : COMPARING) {
                rows.add(written(pair.left()) + " " + op + " " + written(pair.right())
                        + " = " + fold(op, pair.left(), pair.right()));
            }
        }
        return rows;
    }

    /** What {@code left op right} folds to, or that it folds to no constant. Folded against the
     *  real library, which is what a fold is asked of, though a comparison of two literals names
     *  none of it. */
    private static String fold(BinOp op, Hir.Expr left, Hir.Expr right) {
        return ConstEval.against(Symbols.none(DefaultStdlib.get()))
                .eval(new Hir.Binary(op, left, right, CoverageOrigin.unwritten(), POS, null))
                .map(String::valueOf)
                .orElse("not a constant");
    }

    private static String written(Hir.Expr value) {
        return switch (value) {
            case Hir.IntLit i -> String.valueOf(i.value());
            case Hir.BoolLit b -> String.valueOf(b.value());
            default -> throw new IllegalArgumentException("not a value written here: " + value);
        };
    }
}
