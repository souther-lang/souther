package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.diag.CompileException;
import souther.compiler.types.Denotation;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

/**
 * What {@code Resolve} reads a module against: what a name written here means, and the declarations
 * of this compilation as they were written.
 *
 * <p>The counterpart of {@link Symbols}, one representation earlier. The scope is the same object —
 * what a spelling denotes is decided from the names in sight and not from any tree — and the
 * declarations are not: a module {@code Resolve} is resolving against has not been resolved itself,
 * because a name written there is that module's to answer and asking for its resolved form here
 * would be this module waiting on its own.
 *
 * <p>Which is why the two are separate types rather than one holding a stage. There is one reader at
 * this representation and everything else is at the other, so a reader that is handed one of these
 * cannot ask a question only the resolved declarations can answer.
 */
public final class SyntaxSymbols implements NameSense {

    private final TypeScope scope;
    private final Registry<Ast.Def> registry;
    private final Declarations<Ast.Def> declarations;

    private SyntaxSymbols(String module, Registry<Ast.Def> registry, Denoting names) {
        this.scope = new TypeScope(module, names, registry);
        this.registry = registry;
        this.declarations = new Declarations<>(registry, Declarations.Vocabulary.ofNothing());
    }

    /** No module at all — for signatures written over primitives and type variables only. */
    public static SyntaxSymbols none() {
        return new SyntaxSymbols("", Registry.empty(), Denoting.NONE);
    }

    /**
     * A lone module, resolved with nothing else in sight: bare names are its own definitions.
     *
     * <p>The module is indexed here and refused here. This is the door a source comes in at with
     * nowhere for a report to be collected, so a declaration the module may not have is raised as
     * the report — which is what a compilation wants of its own source. What it is not is a lookup
     * that refuses: the raise is at the one statement that builds the table, and what comes out
     * answers every later question about what the module declares.
     */
    public static SyntaxSymbols of(Ast.Module m) {
        DeclaredNames.Index<Ast.Def> declared = Registry.indexed(m);
        if (!declared.refusals().isEmpty()) {
            throw CompileException.of(
                    DeclarationRefusals.reportedAsWritten(declared.refusals().get(0)));
        }
        Map<String, Denotation> names = new HashMap<>();
        for (Ast.Def def : declared.declarations().values()) {
            names.put(def.name(),
                    new Denotation.Denotes(TypeSymbols.declared(def.declaredKey())));
        }
        return new SyntaxSymbols(m.name(),
                Registry.ofRead(Map.of(m.name(), new Registry.Declared<>(
                        declared.declarations(), Registry.baseNames(m.exposing())))),
                Denoting.of(names, Map.of()));
    }

    /** A module resolved against a registry that reads its declarations however it likes — the form
     * a query-backed compilation uses.
     *
     * <p>Reached through {@link Scoping.Scoped#writtenSymbols}, which is where the three that are
     * one answer — the module, its scope and its aliases — come from. A caller free to pass them
     * separately could pass parts of two different assemblies, and nothing it was holding would
     * have said so. */
    public static SyntaxSymbols of(String module, Registry<Ast.Def> registry, Denoting names) {
        return new SyntaxSymbols(module, registry, names);
    }

    /** What a name written here means. */
    @Override
    public TypeScope scope() {
        return scope;
    }

    /** What an identity is a declaration of, as it was written. */
    public Declarations<Ast.Def> declarations() {
        return declarations;
    }

    /**
     * The declarations this module has, each under the identity it is resolved as.
     *
     * <p>What {@code Resolve} reads, and the identity comes with the declaration because they are
     * one fact. Not the declarations the source wrote: a name written twice keeps the first and a
     * built-in case name is refused, both where declarations are indexed, and what is left is what
     * the module declares. A source declaration the module does not have is not one of these, so
     * nothing here has an identity to be resolved under that nothing else would answer with.
     */
    public Map<TypeSymbol, Ast.Def> declaredHere() {
        Map<TypeSymbol, Ast.Def> declared = new LinkedHashMap<>();
        for (Ast.Def def : registry.declaredIn(module()).values()) {
            if (!(scope.resolve(def.written()) instanceof Denotation.Denotes denotes)) {
                // The scope is built from these same declarations, so a module that declares a name
                // and cannot say what it denotes is two answers to one question.
                throw new IllegalStateException("`" + module() + "` declares `" + def.name()
                        + "`, and the scope it is resolved against does not say what it denotes");
            }
            declared.put(denotes.type(), def);
        }
        return declared;
    }

    /** The module being resolved. */
    public String module() {
        return scope.module();
    }

    @Override
    public boolean declares(TypeKey address) {
        return declarations.contains(address);
    }

    @Override
    public Set<String> declaredNamesIn(String module) {
        return declarations.declaredIn(module).keySet();
    }
}
