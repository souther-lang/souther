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

    /** The tree, for the passes of this package that read what this state claims. */
    Hir.Module module() {
        return module;
    }

    /** The behaviors this module declares. */
    public List<Hir.BehaviorDef> behaviors() {
        return module.behaviors();
    }

    /** The names its source offers to whatever reads it, which no stage rewrites. */
    public List<String> exposing() {
        return module.exposing();
    }

    /** Its declarations, which this state says nothing about beyond what the one below it did. */
    public List<Hir.Def> defs() {
        return module.defs();
    }

    /** The example rows attached to this module, from its own file and from every file naming it. */
    public List<Hir.Example> examples() {
        return module.examples();
    }

    /** Its definitions, the taken-on ones not among them — those are what the artifact carries
     * beside what the module wrote. */
    public List<Hir.FnDef> fns() {
        return module.fns();
    }

    /** Which module each imported name came from. */
    public Map<String, String> importedFrom() {
        Map<String, String> packages = new LinkedHashMap<>();
        for (Hir.Import imp : module.imports()) {
            for (String imported : imp.names()) {
                packages.put(imported, imp.module());
            }
        }
        return packages;
    }

    /**
     * This module's artifact with {@code rows} standing where its example rows were — what an
     * example run is given.
     *
     * <p>The rows are a subset because which of them are reported on is an output's question: a
     * module's rows come from its own file and from every {@code examples for} file naming it, and
     * a run reports on one of those files at a time. What does not change with the choice is
     * everything else here, which is what the artifact is.
     */
    public ExampleExecution forExamples(List<Hir.Example> rows) {
        return new ExampleExecution(module, rows);
    }

    /**
     * The rows an example run reads, and the artifact they are evaluated in.
     *
     * <p>Its own type because that pairing is what an example run needs and neither half is enough:
     * the rows say what to try and the artifact says what is there to try it against — the helpers
     * a row applies are methods because this module took them on, and a run that was handed the rows
     * alone would be looking for them in a class that does not carry them.
     *
     * <p>What it claims is about its input and not about its outcome. Nothing here says a row
     * agreed with anything; that is what running them answers.
     */
    public static final class ExampleExecution {

        private final Hir.Module module;
        private final List<Hir.Example> rows;

        private ExampleExecution(Hir.Module module, List<Hir.Example> rows) {
            this.module = module;
            this.rows = List.copyOf(rows);
        }

        /** What the module is called. */
        public String name() {
            return module.name();
        }

        /** The behaviors a row names. */
        public List<Hir.BehaviorDef> behaviors() {
            return module.behaviors();
        }

        /** The definitions the module wrote. */
        public List<Hir.FnDef> fns() {
            return module.fns();
        }

        /** The definitions its artifact carries beside them — what a row applies. */
        public List<Hir.FnDef> takenOn() {
            return module.takenOn();
        }

        /** The rows this run is over. */
        public List<Hir.Example> examples() {
            return rows;
        }

        /** The fake tables its rows run against, which are the module's whole and not one file's:
         * a module's own fakes are what its attached files' rows run against, and the other way
         * round. */
        public List<Hir.Fake> fakes() {
            return module.fakes();
        }
    }

    /**
     * The tree.
     *
     * <p>For a reader asking about the payload rather than about the claim — what shape the module
     * has at this stage, which is a question about the tree and not about what was prepared. What
     * the checks, the adequacy report and the runner read is the parts above, each of which is a
     * projection this state names; a reader wanting one of those asks for it rather than for this.
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
