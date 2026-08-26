package souther.compiler.check;

import souther.compiler.source.SourceId;

import souther.compiler.ast.Hir;
import souther.compiler.diag.CompileException;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

/**
 * The module a check and a codegen run over: its imported names written as the definitions they
 * denote, and the helpers its artifact must carry taken on as its own definitions.
 *
 * <p>Two things and one reason. A name an import brought in is written qualified because that is the
 * spelling the table a call expands against is keyed by, and a definition is taken on because the
 * class this module emits has to hold a method for it. What is taken on is not one kind of thing: a
 * recursive helper another module declared, which cannot be inlined into whoever calls it, and a
 * definition minted here for what a row writes at a position, which has no call site to be inlined
 * into. They arrive for different reasons and leave as the same list, because every reader of it —
 * the expansion table, the check, the backend, the fixture reader — wants the same thing of them,
 * which is that the artifact carries them. Which of the two one is, the definition says
 * ({@link Hir.FnDef#role}).
 *
 * <p>Scoped to the module and not to an output. The classes are emitted once per module
 * ({@code Output.Classes}), and every example row attached to it — from its own file and from every
 * {@code examples for} file naming it — runs against those classes. So what is emitted for a row is
 * emitted over all of them, and which rows are reported on is a question asked later, by
 * {@code Output.Examples}, which carries the source file in its key. A state that took one would be
 * pulling an output's concern up into what the module is.
 *
 * <p>What it holds is parts and not a tree. Each route out of it answers with the state of the part
 * it is for, and the projection writes those back into the shape a whole-module pass takes. The
 * other way round is what this rung used to be: the rungs below answered per declaration and per
 * definition, the assemblies poured the answers into an {@link Hir.Module}, and from here there was
 * nothing left to hand over but nodes.
 */
public final class Prepared {

    private final Desugared.Module desugared;
    private final List<Desugared.Fn> fns;
    private final List<Rows> examples;
    private final List<FakeTable> fakes;
    private final List<Hir.FnDef> takenOn;
    /**
     * The definitions minted for this module's row operands.
     *
     * <p>Their own component, and not among what the module took on. A row's operand is a value this
     * compilation writes for it, reached from a row and from nothing a source can spell — so it is
     * not a declaration a name resolves to, and a table of what names reach has no business holding
     * one. Carried here beside the correspondence they were built with, which is the one walk that
     * knows both.
     */
    private final List<Hir.FnDef> rowDefs;
    /** Which method each row operand's value runs as, by the operand — the correspondence the
     *  emission constructed, held so the reader that invokes a method never counts the rows for
     *  itself. Keyed on operand identity, over the very nodes {@link Rows#read} answers with. */
    private final Map<Hir.Expr, String> operandMethods;
    /** Worked out once, as the rungs below work theirs out. */
    private volatile Hir.Module projected;

    private Prepared(Desugared.Module desugared, List<Desugared.Fn> fns, List<Rows> examples,
                     List<FakeTable> fakes, List<Hir.FnDef> takenOn, List<Hir.FnDef> rowDefs,
                     Map<Hir.Expr, String> operandMethods) {
        this.desugared = desugared;
        this.fns = List.copyOf(fns);
        this.examples = List.copyOf(examples);
        this.fakes = List.copyOf(fakes);
        this.takenOn = List.copyOf(takenOn);
        this.rowDefs = List.copyOf(rowDefs);
        this.operandMethods = operandMethods;
    }

    /** The definitions this module's row operands are, in the order they were emitted. */
    public List<Hir.FnDef> rowDefs() {
        return rowDefs;
    }

    /**
     * {@code desugared} with its imports written out and what its artifact must carry taken on.
     *
     * <p>{@code published} is what the modules this one imports offer it, which is what a row
     * applying one of their helpers is answered from. {@code scope} is what a name in it means,
     * which is what the definitions are held to after they are rewritten. {@code signatures} is
     * what each behavior takes and answers with, which says where a row's values stand — asked of
     * the one place that settles it rather than read back off the forms this module wrote.
     *
     * <p>The rewriting is done a part at a time, and each part's state is established of what came
     * out rather than carried over it. A definition is handed to
     * {@link Desugared.Fn#reestablish}, which proves the proposition again of the rewritten node; a
     * row and a fake table arrive at their state here, because this is the rung that says anything
     * about them.
     *
     * <p>What it does not rewrite is the declarations. Their clauses were written qualified where
     * they were settled, and nothing between there and here puts a name back into one — measured
     * over a compile of the suite, and held by
     * {@code AStateIsReachedOnlyThroughWhatEstablishesItTest}. So they are the answers the rung
     * below gave, and no state is claimed of anything a second time.
     *
     * @throws CompileException where a helper this module reaches cannot be read
     */
    public static Prepared prepare(Desugared.Module desugared, Symbols scope,
                                   Map<String, Hir.FnDef> published,
                                   Map<ValueName.Behavior, Sig> signatures) {
        // An imported definition is written here bare and denotes the module that declares it.
        // Spelling it out, once, settles the name this module reaches it by, which is what the table
        // a call expands against is keyed by and what the method a recursive helper becomes is
        // called. It settles nothing about where the definition came from: the fns below hold
        // declarations of several modules under names of one shape, and which module wrote each is
        // carried on the declaration (Hir.FnDef.declaredIn).
        String self = desugared.name();
        List<Desugared.Fn> fns = new ArrayList<>();
        for (Desugared.Fn fn : desugared.fns()) {
            fns.add(Desugared.Fn.reestablish(HelperNames.qualifyImportsIn(fn.read(), self), scope));
        }
        List<Rows> examples = new ArrayList<>();
        for (Hir.Example block : desugared.module().examples()) {
            examples.add(new Rows(HelperNames.qualifyImportsIn(block, self)));
        }
        List<FakeTable> fakes = new ArrayList<>();
        for (Hir.Fake table : desugared.module().fakes()) {
            fakes.add(new FakeTable(HelperNames.qualifyImportsIn(table, self)));
        }
        Prepared written = new Prepared(desugared, fns, examples, fakes, List.of(), List.of(),
                Map.of());
        // What each row operand computes, emitted beside the module's own so a row runs its operand
        // in the program the behavior it is about is applied in. Which method is whose is kept with
        // the module: it is decided here and read wherever a row is run, never counted out again.
        RowFixtures.Emitted rows = RowFixtures.emitted(written.module(), scope, signatures);
        // Which recursions this module has to emit is not decided here and is not carried from here.
        // It follows from what expanding this module's trees leaves standing, which none of them has
        // been through yet — worked out here, it was a prediction about work not yet done, and it
        // was wrong for every tree the prediction did not know to look at.
        return rows.defs().isEmpty() ? written
                : new Prepared(desugared, fns, examples, fakes, List.of(),
                        List.copyOf(rows.defs().values()), rows.methods());
    }

    /** What the module is called. */
    public String name() {
        return desugared.name();
    }

    /** The behaviors this module declares, which no rung at or below this one rewrites. */
    public List<Hir.BehaviorDef> behaviors() {
        return desugared.behaviors();
    }

    /**
     * Where {@code behavior}'s body comes from (spec §injected-behavior, §unwritten-behavior).
     *
     * <p>How the behavior is written. What a compile emitted for it and what a run can apply are
     * different questions with owners of their own, and this is not an answer to either: a reader
     * wanting to know whether anything will run a behavior asks what will run it.
     *
     * <p>The state and not a flag, so that a reader says which of the two questions about a
     * body-less behavior it is asking: whether there is anything here to run, or whether Java is the
     * one supplying it. Those are the same answer for a behavior with no {@code depends on} and
     * different answers for one that declares it (issue #936).
     */
    public BehaviorImplementation implementationOf(Hir.BehaviorDef behavior) {
        return Requirements.implementationOf(module(), behavior);
    }

    /** Whether {@code behavior}'s body is written here as a {@code let} of its own name, which a
     *  {@code >->} composition's is not. Read from the declarations, so it answers whether or not
     *  this module was elaborated ({@link Requirements#writesItsOwnBody}). */
    public boolean writesItsOwnBody(Hir.BehaviorDef behavior) {
        return Requirements.writesItsOwnBody(module(), behavior);
    }

    /** Whether {@code behavior} is a {@code >->} composition, whose positions, lines and arms are
     *  its stages' ({@link Requirements#isComposition}). */
    public boolean isComposition(Hir.BehaviorDef behavior) {
        return Requirements.isComposition(behavior);
    }

    /** The names its source offers to whatever reads it, which no stage rewrites. */
    public List<String> exposing() {
        return desugared.module().exposing();
    }

    /**
     * Its declarations, each of them the derived declaration and not the node.
     *
     * <p>The answers the rung below gave, handed on. Nothing here rewrites a declaration, so there
     * is nothing that could have made the claim false and no reason to hand over a value that no
     * longer carries it.
     */
    public List<Derived.Def> defs() {
        return desugared.defs();
    }

    /** The example blocks attached to this module, from its own file and from every file naming
     * it, each of them read the way this module reaches its names. */
    public List<Rows> rows() {
        return examples;
    }

    /** Its definitions, the taken-on ones not among them — those are what the artifact carries
     * beside what the module wrote. */
    public List<Desugared.Fn> fns() {
        return fns;
    }

    /** Which module each imported name came from. */
    public Map<String, String> importedFrom() {
        Map<String, String> packages = new LinkedHashMap<>();
        for (Hir.Import imp : desugared.module().imports()) {
            for (String imported : imp.names()) {
                packages.put(imported, imp.module());
            }
        }
        return packages;
    }

    /**
     * Which method each row operand's value runs as, by the operand.
     *
     * <p>The correspondence {@link #prepare} constructed when it emitted the methods, keyed on
     * operand identity. Every reader that needs to know which method is whose reads this; nothing
     * re-derives it by counting rows, because a count over anything but the whole walk is a
     * different numbering.
     */
    public Map<Hir.Expr, String> operandMethods() {
        return operandMethods;
    }

    /**
     * This module's artifact with all of its rows — what an example run over the module is given.
     */
    public Examples forExamples() {
        return new Examples(this, examples);
    }

    /**
     * The same over the rows {@code sourceId} wrote, which each block says of itself.
     *
     * <p>The selection is made here rather than handed in. A module's rows come from its own file
     * and from every {@code examples for} file naming it, and a run reports on one of those files at
     * a time — so what varies is which of these rows, and an operation that took a list of them
     * would be a way to put any rows at all into the state that says these are the module's.
     *
     * <p>Read off each block's own place. A parallel record of where the blocks came from would be
     * the same answer kept somewhere else, and a caller holding one that had fallen out of step had
     * no way to know.
     */
    public Examples forExamplesWrittenIn(SourceId sourceId) {
        List<Rows> mine = new ArrayList<>();
        for (Rows block : examples) {
            if (block.read().pos().isIn(sourceId)) {
                mine.add(block);
            }
        }
        return new Examples(this, mine);
    }

    /**
     * One example block of this module, with every name in it that denotes another module's
     * definition written qualified.
     *
     * <p>Its own type because a reader of one leans on it and would say something else without it:
     * a row whose names are written bare builds no fixture, and what the author is told is that the
     * fixture cannot be built — a report about their model for a reason that is not in it. Measured
     * over a compile of the suite, where the rows qualification touches are the rows whose readings
     * change and no others.
     *
     * <p>Reached from {@link #prepare} and from nothing else.
     */
    public static final class Rows {

        private final Hir.Example block;

        private Rows(Hir.Example block) {
            this.block = block;
        }

        /** The behavior the rows are about. */
        public String target() {
            return block.target();
        }

        /**
         * The block.
         *
         * <p>For a reader that holds this state, as {@link Desugared.Fn#read()} is. What the state
         * says is that the names in it are the ones this module reaches, and a reader that walks
         * the rows has been handed that rather than left to hope for it.
         */
        public Hir.Example read() {
            return block;
        }

        @Override
        public boolean equals(Object o) {
            return o instanceof Rows other && block.equals(other.block);
        }

        @Override
        public int hashCode() {
            return block.hashCode();
        }
    }

    /**
     * One fake table of this module, with every name in it that denotes another module's definition
     * written qualified — the same claim {@link Rows} carries, about what stands in for an
     * injected behavior while a row runs.
     */
    public static final class FakeTable {

        private final Hir.Fake table;

        private FakeTable(Hir.Fake table) {
            this.table = table;
        }

        /**
         * The injected behavior this table stands in for, or null where the name denoted none.
         *
         * <p>The behavior and not the spelling. A table is written where the rows are and the
         * behavior may be declared in another module, so which one it stands in for is what
         * resolution answered and is never worked out again from the characters.
         */
        public ValueName.Behavior standsInFor() {
            return table.standsInFor();
        }

        /** The table, for a reader that holds this state. */
        public Hir.Fake read() {
            return table;
        }

        @Override
        public boolean equals(Object o) {
            return o instanceof FakeTable other && table.equals(other.table);
        }

        @Override
        public int hashCode() {
            return table.hashCode();
        }
    }

    /**
     * The rows an example run reads, and the artifact they are evaluated in.
     *
     * <p>Its own type because that pairing is what an example run needs and neither half is enough:
     * the rows say what to try and the artifact says what is there to try it against — a row's
     * operand is a method because this module emitted one for it, and a run that was handed the rows
     * alone would be looking for it in a class that does not carry it.
     *
     * <p>What it claims is about its input and not about its outcome. Nothing here says a row
     * agreed with anything; that is what running them answers.
     */
    public static final class Examples {

        private final Prepared module;
        private final List<Rows> rows;

        private Examples(Prepared module, List<Rows> rows) {
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
        public List<Desugared.Fn> fns() {
            return module.fns();
        }

        /** Where {@code behavior}'s body comes from. How it is written, and no answer to what will
         *  run it. A fake stands in for an injection target; a row waits for either state with no
         *  body here. */
        public BehaviorImplementation implementationOf(Hir.BehaviorDef behavior) {
            return module.implementationOf(behavior);
        }

        /**
         * The definitions its artifact carries beside them — what a row applies.
         *
         * <p>Nodes, and the boundary is why. What is taken on is another module's definition,
         * reached through what that module published; it comes here from a question that is not a
         * rung of this ladder and holds no proposition to pass on ({@code Bodies.Settled}, measured
         * in #710). A state claimed of one would be claimed of a value nothing here established it
         * of.
         */
        public List<Hir.FnDef> takenOn() {
            return module.takenOn;
        }

        /** The rows this run is over. */
        public List<Rows> rows() {
            return rows;
        }

        /** The fake tables its rows run against, which are the module's whole and not one file's:
         * a module's own fakes are what its attached files' rows run against, and the other way
         * round. */
        public List<FakeTable> fakes() {
            return module.fakes;
        }

        /**
         * The behavior an {@code example} of this module names.
         *
         * <p>A row targets a behavior of the module it is written in (spec §example-evaluable), so
         * a target read off a row is a declaration of this one. Said here because every reader of a
         * row needs it and each restating it would be that rule kept in several places — which is
         * the shape a stand-in's target was in before it carried what it denotes.
         */
        public ValueName.Behavior targeted(String behavior) {
            return new ValueName.Behavior(name(), behavior);
        }

        /**
         * The table that stands in for {@code dependency}, or null where none does.
         *
         * <p>The first one written for it, which is the rule the whole module is read under: a
         * second table for one dependency is never reached, so it stands in for nothing, is
         * compared against nothing, and is not built (spec §example-fakes, §example-pending). A
         * table whose target denotes no behavior stands in for nothing either, and is refused where
         * its name is read.
         *
         * <p>One place, because a run picking a table, a reading comparing one against the recorded
         * rows, and a build of the tables that answer would otherwise be three walks agreeing by
         * hand — and the day they stopped agreeing, a row would run against a table nothing was
         * holding to anything.
         */
        public FakeTable standingInFor(ValueName.Behavior dependency) {
            for (FakeTable table : module.fakes) {
                if (dependency.equals(table.standsInFor())) {
                    return table;
                }
            }
            return null;
        }

        /** Every dependency a table here stands in for, each under the table that answers for it,
         *  in the order the tables are written. */
        public LinkedHashMap<ValueName.Behavior, FakeTable> tablesThatAnswer() {
            LinkedHashMap<ValueName.Behavior, FakeTable> answering = new LinkedHashMap<>();
            for (FakeTable table : module.fakes) {
                if (table.standsInFor() != null) {
                    answering.putIfAbsent(table.standsInFor(), table);
                }
            }
            return answering;
        }

        /**
         * Every behavior this module writes a stand-in for: the target of a {@code fake} and the
         * dependency a {@code with} on a row supplies.
         *
         * <p>Both forms, because both are stand-ins (spec §example-fakes) and a reader asking what
         * this module states about a behavior wants either. Told apart from
         * {@link #tablesThatAnswer}, which asks which *table* answers for a dependency: a
         * {@code with} writes no table, so a reader taking that answer for this one passes over
         * every behavior a row supplies without one — which is how a {@code with} for a dependency
         * another module declares came to be compared against nothing.
         *
         * <p>What is written and not what is comparable. Whether a stand-in can be held against a
         * recorded row turns on what the dependency takes, and that is the reading's question to
         * ask; this one is answered from the text.
         *
         * <p>The module's, not one file's, as {@link #fakes} is: a module's stand-ins are what its
         * attached files' rows run against and the other way round, so which modules a reading has
         * to take the rows of is a fact about the module. Read off {@link #rows} it would be one
         * file's {@code with}s wherever this is a projection of a source, and the modules the other
         * files reach would go unread — which is the reading this answer exists to complete.
         */
        public Set<ValueName.Behavior> standsInFor() {
            Set<ValueName.Behavior> named = new LinkedHashSet<>(tablesThatAnswer().keySet());
            for (Rows block : module.examples) {
                for (Hir.ExampleRow row : block.read().rows()) {
                    for (Hir.With supplied : row.withs()) {
                        if (supplied.standsInFor() != null) {
                            named.add(supplied.standsInFor());
                        }
                    }
                }
            }
            return named;
        }

        /** Which method each row operand runs as, whole-module like the fakes: the methods were
         * emitted over every file's rows, so a run over one file's reads the correspondence the
         * emission constructed rather than numbering its own subset from zero. */
        public Map<Hir.Expr, String> operandMethods() {
            return module.operandMethods();
        }

        /** The artifact the rows run in. */
        Hir.Module module() {
            return module.module();
        }
    }

    /**
     * The parts written back into the shape a pass over a whole module takes.
     *
     * <p>Built in one place and never read back into parts. This is where the module leaves the
     * ladder: {@code Lower.settle} hands it to a pass that settles helper parameter types across
     * the whole of it, and what that answers with is a tree carrying no proposition — measured in
     * #710, which is why {@code Bodies.Settled} is not a rung.
     */
    Hir.Module module() {
        Hir.Module built = projected;
        if (built != null) {
            return built;
        }
        List<Hir.FnDef> definitions = new ArrayList<>();
        for (Desugared.Fn fn : fns) {
            definitions.add(fn.read());
        }
        List<Hir.Example> blocks = new ArrayList<>();
        for (Rows block : examples) {
            blocks.add(block.read());
        }
        List<Hir.Fake> tables = new ArrayList<>();
        for (FakeTable table : fakes) {
            tables.add(table.read());
        }
        projected = built = desugared.module().withFns(definitions).withExamples(blocks)
                .withFakes(tables).withTakenOn(takenOn);
        return built;
    }

    /**
     * The same, for the tests that audit what a module carries at each stage.
     *
     * <p>They ask about the payload rather than about the claim. What the checks, the adequacy
     * report and the runner read is the parts above, each of which is what this state has to say
     * about that part; a reader wanting one of those asks for it rather than for this.
     */
    public Hir.Module tree() {
        return module();
    }

    /**
     * Everything this state answers with.
     *
     * <p>Not the projection alone. The tree carries what the module declared and what it writes; the
     * definitions minted for its rows are beside it and are in no tree, so two states whose trees
     * compare equal can still say different things about the rows. They do, and without touching the
     * source: a row's operand is wrapped in the type the position it stands at contributes, and that
     * position comes from a behavior's signature — which an edit to an imported module can change
     * while this module's text stays as it was.
     *
     * <p>A state is a query's answer, and a store decides whether anything downstream has to be
     * asked again by comparing the answer it recomputed with the one it held. An answer that leaves
     * out what it answers with is one the store cannot tell has changed.
     *
     * <p>The correspondence between an operand and its method is left out on purpose: it is keyed on
     * operand identity, over the very nodes the tree hands out, so it says nothing a tree and the
     * definitions built from it do not already say.
     */
    @Override
    public boolean equals(Object o) {
        return o instanceof Prepared other && module().equals(other.module())
                && rowDefs.equals(other.rowDefs);
    }

    @Override
    public int hashCode() {
        return module().hashCode() * 31 + rowDefs.hashCode();
    }
}
