package souther.compiler.partition;

import souther.compiler.ast.Ast;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Place;

/**
 * The count a written value stands for.
 *
 * <p>What a number comes to as a quantity is {@link souther.compiler.numeric.CountDomain}'s; this is
 * the step before it, reading a count off what a fixture wrote.
 */
final class Counts {

    /**
     * The count a fixture settles its position at, reaching through the newtype it may be wrapped
     * in, or null where it settles none.
     *
     * <p>Only a written number. A temporal fixture carries its text and not its count, and it stays
     * unsettled rather than being read back: what a settled position is for is asking the record's
     * rules what is left beside it, and those rules are read over the positions the projection
     * holds — which the temporal ones are not yet.
     *
     * <p>Here rather than beside either walk. Both of them settle a field before choosing the next,
     * and two readings of what a written value counts as are two chances to settle different
     * things.
     */
    static Place writtenIn(Ast.Expr written) {
        return switch (written) {
            case Ast.IntLit i -> Count.of(i.value());
            case Ast.DecimalLit d -> Count.of(d.value());
            case Ast.Neg n -> {
                Place inner = writtenIn(n.operand());
                yield inner == null ? null : Count.number(inner).negate();
            }
            case Ast.Apply a when a.args().size() == 1 -> writtenIn(a.args().get(0));
            case null, default -> null;
        };
    }

    private Counts() {}
}
