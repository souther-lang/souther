package souther.compiler.check;

import souther.compiler.DefaultStdlib;
import souther.compiler.ast.Hir;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BinOp;
import souther.compiler.types.SourceConstructOrigin;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * An expression written with a comparing operator folds to what the relation that operator placed
 * comes to of its two sides.
 *
 * <p>The way from the operator to the answer, taken whole: what the operator placed
 * ({@link ComparisonPlacement}), the relation that placement states, and the fold of that relation
 * over two constants. Every operator that compares is put through it, because what is being fixed
 * is the way and not any one relation — a claim read off the wrong operator answers every question
 * a reader can ask of it, and answers them about a comparison nobody wrote.
 *
 * <p><b>Which operators those are is asked of the operator.</b> Written out here, this would be a
 * second membership beside {@link BinOp#compares} — the one it is asked of everywhere else — and
 * the two can be given different answers about an operator added later. Written out, the operator
 * added later is folded by nothing here and this stays green while saying "every".
 *
 * <p>What the relations themselves come to is fixed against how two values stand, and not here.
 */
class AComparisonFoldsToWhatItsOperatorPlacedTest {

    private static final SourcePos POS = new SourcePos(1, 1);

    /** Every operator that compares, asked of the operator. */
    private static final List<BinOp> COMPARING =
            Stream.of(BinOp.values()).filter(BinOp::compares).toList();

    /** What a fold that answers no constant is said as, which is what the callers read empty as. */
    private static final String NOT_A_CONSTANT = "not a constant";

    /** Two written values, and what folding each comparison of them comes to. */
    private record Written(String left, String right, Hir.Expr leftValue, Hir.Expr rightValue,
                           Map<BinOp, String> folds) { }

    private static final List<Written> PAIRS = List.of(
            new Written("1", "2", intLit(1), intLit(2), Map.of(
                    BinOp.LT, "true", BinOp.LE, "true", BinOp.GT, "false", BinOp.GE, "false",
                    BinOp.EQ, "false", BinOp.NE, "true")),
            new Written("2", "2", intLit(2), intLit(2), Map.of(
                    BinOp.LT, "false", BinOp.LE, "true", BinOp.GT, "false", BinOp.GE, "true",
                    BinOp.EQ, "true", BinOp.NE, "false")),
            new Written("2", "1", intLit(2), intLit(1), Map.of(
                    BinOp.LT, "false", BinOp.LE, "false", BinOp.GT, "true", BinOp.GE, "true",
                    BinOp.EQ, "false", BinOp.NE, "true")),
            // No order to answer an ordering by, and an equality all the same.
            new Written("true", "true", boolLit(true), boolLit(true), Map.of(
                    BinOp.LT, NOT_A_CONSTANT, BinOp.LE, NOT_A_CONSTANT,
                    BinOp.GT, NOT_A_CONSTANT, BinOp.GE, NOT_A_CONSTANT,
                    BinOp.EQ, "true", BinOp.NE, "false")),
            new Written("true", "false", boolLit(true), boolLit(false), Map.of(
                    BinOp.LT, NOT_A_CONSTANT, BinOp.LE, NOT_A_CONSTANT,
                    BinOp.GT, NOT_A_CONSTANT, BinOp.GE, NOT_A_CONSTANT,
                    BinOp.EQ, "false", BinOp.NE, "true")));

    @Test
    void everyComparingOperatorFoldsToWhatItPlacedOverTwoConstants() {
        Map<String, String> written = new LinkedHashMap<>();
        Map<String, String> folded = new LinkedHashMap<>();
        for (Written pair : PAIRS) {
            for (BinOp op : COMPARING) {
                String row = pair.left() + " " + op + " " + pair.right();
                written.put(row, pair.folds().get(op));
                folded.put(row, fold(op, pair.leftValue(), pair.rightValue()));
            }
        }
        assertEquals(written, folded);
    }

    /**
     * What is written below is an answer for each operator that compares, and for no other.
     *
     * <p>The two sets are made differently on purpose — one is asked of the operator, the other is
     * what somebody wrote out — so holding them against each other is what says an operator added
     * to the language is folded here rather than passed over in silence. It is also what says the
     * fold above ran at all: two empty sets agree, and these do not.
     */
    @Test
    void whatIsWrittenOutCoversEveryOperatorThatCompares() {
        List<Set<BinOp>> asked = new ArrayList<>();
        List<Set<BinOp>> answered = new ArrayList<>();
        for (Written pair : PAIRS) {
            asked.add(Set.copyOf(COMPARING));
            answered.add(pair.folds().keySet());
        }
        assertEquals(asked, answered,
                "an operator that compares and is not written out here is folded by nothing");
    }

    /** What {@code left op right} folds to. Folded against the real library, which is what a fold
     *  is asked of, though a comparison of two literals names none of it. */
    private static String fold(BinOp op, Hir.Expr left, Hir.Expr right) {
        return ConstEval.against(Symbols.none(DefaultStdlib.get()))
                .eval(new Hir.Binary(op, left, right, SourceConstructOrigin.unwritten(), POS, null))
                .map(String::valueOf)
                .orElse(NOT_A_CONSTANT);
    }

    private static Hir.Expr intLit(long value) {
        return new Hir.IntLit(value, POS, null);
    }

    private static Hir.Expr boolLit(boolean value) {
        return new Hir.BoolLit(value, POS, null);
    }
}
