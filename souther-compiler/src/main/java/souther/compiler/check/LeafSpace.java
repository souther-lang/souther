package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * The leaves a type is made of: the cases it can be that are not themselves sums.
 *
 * <p>A sum whose case is a sum is transparent as a value — anything of the inner one is of the
 * outer one (spec §sum-data) — so what a value of the outer sum can be is not its case list but
 * what descending that list reaches. That descent is what this is, and it is written once. Four
 * readers used to write it themselves, each keyed on what suited it, and they answered differently
 * where the descent reaches one leaf twice.
 *
 * <p>A leaf is one per {@link TypeSymbol}. Two cases naming one type are one leaf however many
 * declarations reach it: the type is what a value is, what a codec tags, and what an arm tests, so
 * a reader keyed on anything else counts one thing as two.
 *
 * <p>What comes out is unique and in the order the declarations first reach each leaf. Not a bare
 * set: a derived codec's variants are written in it (spec §sum-discrimination), so an order that
 * came out of whichever collection was reached for would move a generated artifact nothing about
 * the program had changed.
 */
public final class LeafSpace {

    private LeafSpace() {}

    /**
     * What a value of {@code t} can be, descending every case that is itself a sum.
     *
     * <p>Answers for anything, not only a sum: a type that is no sum is the one leaf it is, and a
     * type that names nothing at all — {@code Raw}, a type the compiler could not work out — has
     * none. Which of those a reader treats as an answer and which as a refusal is the reader's, and
     * asking here does not decide it.
     */
    public static List<TypeSymbol> leavesOf(Type t, Symbols symbols) {
        Set<TypeSymbol> leaves = new LinkedHashSet<>();
        descend(TypeOps.namesOf(t), symbols, leaves, new HashSet<>());
        return List.copyOf(leaves);
    }

    /** The same, of what a sum declares — its own name is not a leaf of it. */
    public static List<TypeSymbol> leavesOf(Hir.SumData sum, Symbols symbols) {
        Set<TypeSymbol> leaves = new LinkedHashSet<>();
        descend(TypeOps.caseNames(sum), symbols, leaves, new HashSet<>());
        return List.copyOf(leaves);
    }

    /**
     * Collects the leaves under {@code names}, descending the ones that are sums.
     *
     * <p>{@code visiting} is what a sum reaching itself terminates on. Such a declaration is
     * reported where it is written ({@link DataChecker}); this only has to come back.
     */
    private static void descend(Iterable<TypeSymbol> names, Symbols symbols,
                                Set<TypeSymbol> leaves, Set<TypeSymbol> visiting) {
        for (TypeSymbol name : names) {
            if (symbols.declarations().declaration(name.key()) instanceof Hir.SumData sum) {
                if (visiting.add(name)) {
                    descend(TypeOps.caseNames(sum), symbols, leaves, visiting);
                }
            } else {
                leaves.add(name);
            }
        }
    }
}
