package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.ast.Hir;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.Map;

/**
 * What a semantic identity is a declaration of.
 *
 * <p>The other half of what a module needs, and not the half {@link Scope} answers: this takes an
 * identity and never a spelling, so nothing here has to know which module is being compiled. A
 * reader holding one of these has already resolved whatever it is asking about.
 *
 * <p>{@code D} is the representation the declarations are in, and a representation is all it is.
 * Everything below {@code Resolve} holds {@link Hir}; {@code Resolve} reads the declarations of the
 * modules it resolves against as they were written, because a name written there is that module's to
 * resolve and not this one's. What {@code D} does not say is how far the declarations have got,
 * because the two sources below have got different distances — the language's vocabulary is loaded
 * resolved and derivation never runs over it — so a {@code D} naming a rung would be false of one of
 * them. Which rung a reader is at is which of these it was handed.
 *
 * <p>Two sources, kept apart. {@link Registry} is what this compilation declares, read one
 * declaration at a time; the language's own vocabulary — the prelude's runtime-backed data — is
 * declared by no module of the compilation and is answered beside it. {@link #declaration} sees
 * both, because a name that denotes one types like a name that denotes the other;
 * {@link #declaredByCompilation} sees only the first, because what a compilation may construct is
 * governed by {@code constructs} and the language's vocabulary is not.
 *
 * <p>Asked one identity at a time. {@link #declaredIn} enumerates, for the questions that really are
 * about a whole module — which sum a case belongs to, what a "did you mean" may offer — and is not
 * how {@link #declaration} is answered. Reading a module's declarations to reach one of them makes
 * the reader depend on all of them, and the failure of any one of them becomes the failure of every
 * question about the rest.
 */
public final class Declarations<D> {

    private final Registry<D> registry;
    private final Vocabulary<D> language;

    Declarations(Registry<D> registry, Vocabulary<D> language) {
        this.registry = registry;
        this.language = language;
    }

    /**
     * What the language itself declares, as the reader asking holds declarations.
     *
     * <p>The prelude's runtime-backed data is loaded resolved, so it is there to be answered with
     * only where the reader holds {@link Hir}. A reader at the written representation is
     * {@code Resolve}, which reaches a declaration to walk what it includes, and nothing the
     * language declares is included from — {@link #ofNothing} says that once, rather than as a null
     * every caller has to know about.
     */
    public interface Vocabulary<D> {

        /** The declaration this identity names, or null where the language declares none. */
        D declaration(TypeKey address);

        /** Everything it declares, keyed by bare name. */
        Map<String, D> declaredIn();

        /** The language's own vocabulary, as a resolved compilation reads it. */
        static Vocabulary<Hir.Def> ofLanguage() {
            return new Vocabulary<>() {
                @Override
                public Hir.Def declaration(TypeKey address) {
                    return Prelude.runtimeBackedDef(address);
                }

                @Override
                public Map<String, Hir.Def> declaredIn() {
                    return Prelude.runtimeBackedDefs();
                }
            };
        }

        /** Nothing beside what the compilation itself declares. */
        static Vocabulary<Ast.Def> ofNothing() {
            return new Vocabulary<>() {
                @Override
                public Ast.Def declaration(TypeKey address) {
                    return null;
                }

                @Override
                public Map<String, Ast.Def> declaredIn() {
                    return Map.of();
                }
            };
        }
    }

    /** The declaration {@code name} names, or null when nothing declares it. */
    public D declaration(TypeKey address) {
        D def = registry.declaration(address);
        return def != null ? def : language.declaration(address);
    }

    /** Whether anything declares {@code name} — this compilation or the language. */
    public boolean contains(TypeKey address) {
        return declaration(address) != null;
    }

    /**
     * The identity of the declaration that address names, or null where nothing declares it.
     *
     * <p>{@link Registry#identify} over both sources, for a reader whose address came from outside
     * the compiler — a binary name read off a live value is one. Asking rather than assembling: an
     * address is not an identity until something declares one there, so a reader that gets nothing
     * back has nothing it could have gone on with, and one that gets an identity has been told a
     * declaration is behind it.
     */
    public TypeSymbol identify(TypeKey address) {
        return contains(address) ? TypeSymbols.declared(address) : null;
    }

    /** Whether {@code name} is declared by a module of this compilation — as opposed to a
     * declaration the language gives (the prelude's runtime-backed data), which resolves and types
     * like any other but belongs to no module here. The construction discipline asks this: what a
     * compilation declares is governed by {@code constructs}; the language's vocabulary is not. */
    public boolean declaredByCompilation(TypeKey address) {
        return registry.declaration(address) != null;
    }

    /** Every definition of one module, keyed by the name written there. The runtime namespace
     * answers with the prelude's runtime-backed data. */
    public Map<String, D> declaredIn(String moduleName) {
        if (souther.compiler.types.TypeSymbol.RUNTIME.equals(moduleName)) {
            return language.declaredIn();
        }
        return registry.declaredIn(moduleName);
    }
}
