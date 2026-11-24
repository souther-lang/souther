package souther.compiler.partition;

import souther.compiler.ast.Hir;
import souther.compiler.core.IntNegation;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Place;

import java.util.function.BiConsumer;

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
    static Place writtenIn(Hir.Expr written) {
        return switch (written) {
            case Hir.IntLit i -> Count.of(i.value());
            case Hir.DecimalLit d -> Count.of(d.value());
            case Hir.Neg n when IntNegation.isTheLeastInt(n.operand()) -> null;
            case Hir.Neg n -> {
                Place inner = writtenIn(n.operand());
                yield inner == null ? null : Count.number(inner).negate();
            }
            case Hir.Apply a when a.args().size() == 1 -> writtenIn(a.args().get(0));
            case null, default -> null;
        };
    }

    /**
     * Every count a value settles, at the place under {@code at} it settles it: through the fields
     * of a record built field by field, and through a name wrapping one.
     *
     * <p>What a rule of a value around the one written is told of it. A rule relating two fields of
     * an inner record is asked what the first came to before the second is chosen, and the first
     * is a field of whatever record it was built in.
     */
    static void writtenUnder(TermPath at, Hir.Expr written, BiConsumer<TermPath, Count> into) {
        switch (written) {
            case Hir.NewData data -> {
                for (Hir.FieldInit each : data.inits()) {
                    writtenUnder(at.then(each.written().canonical()), each.value(), into);
                }
            }
            case Hir.Apply a when a.args().size() == 1 -> writtenUnder(at, a.args().get(0), into);
            case null, default -> {
                if (writtenIn(written) instanceof Count count) {
                    into.accept(at, count);
                }
            }
        }
    }

    private Counts() {}
}
