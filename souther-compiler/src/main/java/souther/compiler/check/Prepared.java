package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.diag.CompileException;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * The module a check and a codegen run over: its imported names written as the definitions they
 * denote, and the helpers its artifact must carry taken on as its own definitions.
 *
 * <p>Two things and one reason. A name an import brought in is written qualified because that is the
 * spelling the table a call expands against is keyed by, and a helper is taken on because the class
 * this module emits has to hold a method for it. What is taken on is not one kind of thing: a
 * recursive helper cannot be inlined, and a helper an example row applies is run rather than expanded
 * into the row (ADR-0077). They arrive for different reasons and leave as the same list, because
 * every reader of it — the expansion table, the check, the backend, the fixture reader — wants the
 * same thing of them, which is that the artifact carries them.
 *
 * <p>Scoped to the module and not to an output. The classes are emitted once per module
 * ({@code Output.Classes}), and every example row attached to it — from its own file and from every
 * {@code examples for} file naming it — runs against those classes. So the helpers a row applies are
 * gathered over all of them, and which rows are reported on is a question asked later, by
 * {@code Output.Examples}, which carries the source file in its key. A state that took one would be
 * pulling an output's concern up into what the module is.
 */
public final class Prepared {

    private final Hir.Module module;

    private Prepared(Hir.Module module) {
        this.module = module;
    }

    /**
     * {@code desugared} with its imports written out and what its artifact must carry taken on.
     *
     * <p>{@code published} is what the modules this one imports offer it, which is what a row
     * applying one of their helpers is answered from.
     *
     * @throws CompileException where a helper this module reaches cannot be read
     */
    public static Prepared prepare(Desugared.Module desugared, Map<String, Hir.FnDef> published) {
        // An imported definition is written here bare and denotes the module that declares it.
        // Spelling it out, once, settles the name this module reaches it by, which is what the table
        // a call expands against is keyed by and what the method a recursive helper becomes is
        // called. It settles nothing about where the definition came from: the fns below hold
        // declarations of several modules under names of one shape, and which module wrote each is
        // carried on the declaration (Hir.FnDef.declaredIn).
        Hir.Module m = HelperNames.qualifyImports(desugared.module());
        HelperInliner inliner = HelperInliner.forModule(m, published);
        Map<String, Hir.FnDef> injected = new LinkedHashMap<>(inliner.injectedRecursiveHelpers());
        // A helper an example row applies is emitted for that reason (ADR-0077); one this module
        // does not declare is taken on here, as a recursive one it reaches is.
        inliner.injectedExampleHelpers().forEach(injected::putIfAbsent);
        if (injected.isEmpty()) {
            return new Prepared(m);
        }
        // Beside what the module declared, not among it. Both are emitted and only the first was
        // written here, and a reader asking which is which asks the component it is in rather than
        // the shape of a name.
        return new Prepared(new Hir.Module(m.name(), m.exposing(), m.exposedOutputs(), m.imports(),
                m.defs(), m.behaviors(), m.fns(), List.copyOf(injected.values()), m.examples(),
                m.fakes(), m.exampleFileTarget(), m.pos()));
    }

    /** What the module is called. */
    public String name() {
        return module.name();
    }

    /**
     * The tree.
     *
     * <p>What every reader below this takes, and the seam the rest of this migration closes. The
     * checks, the adequacy report, the backend and the editor each read a part of this module — the
     * behaviors, the declarations, the definitions — and each of those is a projection this state
     * has yet to name. Until it does, the claim is what the query answered with and is dropped here.
     */
    public Hir.Module tree() {
        return module;
    }

    @Override
    public boolean equals(Object o) {
        return o instanceof Prepared other && module.equals(other.module);
    }

    @Override
    public int hashCode() {
        return module.hashCode();
    }
}
