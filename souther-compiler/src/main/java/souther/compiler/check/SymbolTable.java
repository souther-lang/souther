package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.core.Kernel;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

/**
 * A {@link TypeScope} and a {@link Declarations} together, in the representation the declarations
 * are in.
 *
 * <p>The state behind {@link ResolvedSymbols} and {@link DerivedSymbols}, held once rather than
 * written out in each. It is not what a reader is given: which stage's declarations these are is the
 * whole of what those two say, and a reader handed this instead would be holding the pair with
 * nothing saying which world it is the pair of.
 *
 * <p>{@code D} is the representation the declarations are in, and a representation is all it is.
 * Which rung a reader is at is which of the two carriers it was handed.
 *
 * <p>How a declaration is read off one of them is handed in rather than asked of {@code D}. A
 * member every stage's carrier answers would have to mean the same thing at every stage, and it does
 * not: what a resolved node hands over is what was written, and what a normalized declaration hands
 * over has had its constructions rewritten. Written as an interface, the two would be one word for
 * two things, which is what a reader at the far end of a table has no way to tell apart.
 */
final class SymbolTable<D> {

    private final TypeScope scope;
    private final Declarations<D> declarations;
    /** How the declaration node is read off one of these. */
    private final Function<D, Hir.Def> node;
    /** The library this module is compiled against. Held so that a reader already holding the
     *  symbol table has it — what a library operation is declared to be is part of what names mean
     *  here, and a reader that fetched its own could be reading a different library from the one
     *  this module's names were resolved against. */
    private final Stdlib stdlib;

    SymbolTable(String module, Registry<D> registry, Denoting names,
                Declarations.Vocabulary<D> language, Stdlib stdlib, Function<D, Hir.Def> node) {
        this.scope = new TypeScope(module, names, registry, stdlib.names().languageTypes());
        this.declarations = new Declarations<>(registry, language);
        this.stdlib = stdlib;
        this.node = node;
    }

    TypeScope scope() {
        return scope;
    }

    Declarations<D> declarations() {
        return declarations;
    }

    Stdlib library() {
        return stdlib;
    }

    /** The declaration {@code name} is, in the representation this table holds, or null where
     *  nothing declares one. */
    Hir.Def declaredNode(TypeSymbol name) {
        D def = declarations.declaration(name);
        return def == null ? null : node.apply(def);
    }

    /** The same, of an address. */
    Hir.Def declaredNode(TypeKey address) {
        D def = declarations.declaration(address);
        return def == null ? null : node.apply(def);
    }

    boolean declares(TypeKey address) {
        return declarations.contains(address);
    }

    boolean declaredByCompilation(TypeSymbol name) {
        return declarations.declaredByCompilation(name);
    }

    boolean declaredByCompilation(TypeKey address) {
        return declarations.declaredByCompilation(address);
    }

    Set<String> declaredNamesIn(String module) {
        return declarations.declaredIn(module).keySet();
    }

    String module() {
        return scope.module();
    }

    ValueName.Stdlib.Operation theWalk() {
        return stdlib.theWalk();
    }

    ValueName.Stdlib.Operation theDistinctnessPredicate() {
        return stdlib.theDistinctnessPredicate();
    }

    Kernel kernelOf(ValueName.Stdlib.Operation operation) {
        Stdlib.Intrinsic intrinsic = stdlib.intrinsicOf(operation);
        return intrinsic == null ? null : intrinsic.kernel();
    }

    /** Every bare spelling that reaches a definition here, and the definition it reaches. */
    Map<String, D> reachable() {
        Map<String, D> reached = new LinkedHashMap<>();
        scope.denotedNames().forEach((spelling, name) -> {
            D def = declarations.declaration(name);
            if (def != null) {
                reached.put(spelling, def);
            }
        });
        return reached;
    }
}
