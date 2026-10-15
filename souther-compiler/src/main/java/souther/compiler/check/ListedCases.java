package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;

import java.util.List;
import java.util.function.Function;

/**
 * The cases a sum lists: one layer, in the order it writes them, each the declaration the name
 * written there denotes.
 *
 * <p>Beside {@link PublishedDeclarations} and not read off it, for the reason {@link DeclarationKinds}
 * is. Which cases a sum lists is settled where the names in it resolve, and nothing below changes
 * it; what a declaration says is worked out later, out of the module with its clauses settled. A
 * reader that only has to know what a sum is made of depends on the first and not the second, which
 * is what lets it ask while a declaration's meaning is being made — a helper an invariant calls is
 * typed then, and a {@code match} in it asks what its subject's cases are.
 *
 * <p>One layer, and not the leaves under it. What descending it reaches is {@link AtomSpace}'s to
 * work out, and what a value of a sum can be is {@link SumCases}'.
 */
@FunctionalInterface
public interface ListedCases {

    /**
     * The cases {@code sum} lists, or null where nothing declares a sum there.
     *
     * <p>Asked of a name {@link DeclarationKinds} has already said is a sum. Whether a name is one is
     * a question about its form, and reading a declaration to answer it would read a product too.
     */
    List<TypeSymbol> of(TypeKey sum);

    /** Nothing declared anywhere — for a reading over primitives, which asks of no declaration. */
    ListedCases NONE = _ -> null;

    /**
     * The same question read off {@code symbols}' declarations, which is where a reader holding a
     * scope finds the sums of this compilation and of the language alike.
     */
    static ListedCases asWritten(Symbols symbols) {
        return readOff(symbols::declaredNode);
    }

    /**
     * The same question read off whatever {@code declarations} answers for an address, for a reader
     * that holds the declarations and no scope to read them in.
     *
     * <p>Every way of asking this comes here, so a sum's one layer is read in one place whichever
     * representation of the declarations a reader holds.
     */
    static ListedCases readOff(Function<TypeKey, Hir.Def> declarations) {
        return sum -> declarations.apply(sum) instanceof Hir.SumData declared
                ? TypeOps.caseNames(declared)
                : null;
    }
}
