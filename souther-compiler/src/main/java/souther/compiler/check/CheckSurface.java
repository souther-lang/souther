package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.diag.CompileException;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * The module a best-effort reading of a compilation runs over, assembled once.
 *
 * <p>It carries no claim that every declaration derived or that the module can be emitted. What it
 * is, is the one place the parts are put together: an imported name written as the definition it
 * denotes, a definition held to what it came out as, an example and a fake table written the same
 * way, and a definition minted for what each row writes at a position. Every reader that wants a
 * whole module to walk over gets it from here, so those are decided once and never counted out
 * again.
 *
 * <p>Its declarations are the ones {@link Normalized} answered for, handed in rather than worked out
 * here: failing to derive a representation does not put an earlier spelling back into the tree. A
 * module holding one declaration that could not be derived is still read for what its other
 * definitions say, and the declaration that could not be derived is here in the form every reader
 * below the settling expects — not beside them in a spelling one rung up, which nothing in a tree
 * would say was different.
 *
 * <p>Not a rung, and it says so ({@link Assembly}). What a state of this package says is that
 * something was established of a value; what this says is where the parts were joined.
 * {@link Prepared} is the state — it is this assembly beside the witness that every declaration came
 * out — and a reader that has to have a whole module asks for that one.
 */
public final class CheckSurface implements Assembly {

    /** The settling the parts were joined over, kept rather than its tree: what a pass reads off
     *  this is the tree, and what says which module it is an assembly of is the state. */
    private final InvariantSettled settling;
    private final List<Normalized.Def> declarations;
    private final List<Desugared.Fn> fns;
    private final List<Hir.Example> examples;
    private final List<Hir.Fake> fakes;
    private final List<Hir.FnDef> rowDefs;
    private final Map<Hir.Expr, String> operandMethods;
    /** Worked out once, as the rungs beside this work theirs out. */
    private volatile Hir.Module projected;

    private CheckSurface(InvariantSettled settling, List<Normalized.Def> declarations,
                         List<Desugared.Fn> fns,
                         List<Hir.Example> examples, List<Hir.Fake> fakes,
                         List<Hir.FnDef> rowDefs, Map<Hir.Expr, String> operandMethods) {
        this.settling = settling;
        this.declarations = List.copyOf(declarations);
        this.fns = List.copyOf(fns);
        this.examples = List.copyOf(examples);
        this.fakes = List.copyOf(fakes);
        this.rowDefs = List.copyOf(rowDefs);
        this.operandMethods = operandMethods;
    }

    /**
     * The parts of {@code settling} joined.
     *
     * <p>{@code normalized} is the declarations as the one producer of that form answered for them
     * ({@code Shapes.NormalizedDeclarations}), handed in rather than worked out again here. Worked
     * out here, this would be a second producer of the normalized form, and a declaration read off
     * this surface could differ from the same one read anywhere else. {@code desugared} is the
     * definitions that came out, which may be short of what the module wrote: a definition is worked
     * out whether or not the one before it came out.
     *
     * <p>{@code scope} is what a name means below the derivation, which is what a definition is held
     * to after it is rewritten; {@code signatures} is what each behavior takes and answers with,
     * which says where a row's values stand.
     *
     * <p>Null where a part the module writes is not among what was handed in — a declaration that
     * was not normalized, a definition that did not desugar. What this carries is the module, and a
     * module short of something it writes is read as one that does not write it, which is how a name
     * a module exposes came back as a name it must have imported. That a representation could not be
     * derived for a declaration is the other thing entirely, and costs this nothing: the declaration
     * is here, and what it says about itself is read from it.
     *
     * @throws CompileException where a definition cannot be held to what it was rewritten to
     */
    public static CheckSurface assemble(InvariantSettled settling,
                                        Map<String, Normalized.Def> normalized,
                                        Map<String, Desugared.Fn> desugared, Symbols scope,
                                        Map<ValueName.Behavior, Sig> signatures) {
        Hir.Module settled = settling.module();
        List<Normalized.Def> declarations = new ArrayList<>();
        for (InvariantSettled.Def def : settling.defs()) {
            Normalized.Def came = normalized.get(def.name());
            if (came == null) {
                return null;
            }
            declarations.add(came);
        }
        // An imported definition is written here bare and denotes the module that declares it.
        // Spelling it out, once, settles the name this module reaches it by, which is what the table
        // a call expands against is keyed by and what the method a recursive helper becomes is
        // called.
        String self = settled.name();
        // In the order the module wrote them, and not the order they were worked out in: what a
        // report about two definitions wrong the same way names is the earlier of them.
        List<Desugared.Fn> fns = new ArrayList<>();
        for (Hir.FnDef wrote : settled.fns()) {
            Desugared.Fn came = desugared.get(wrote.name());
            if (came == null) {
                return null;
            }
            fns.add(Desugared.Fn.reestablish(
                    HelperNames.qualifyImportsIn(came.read(), self), scope));
        }
        List<Hir.Example> examples = new ArrayList<>();
        for (Hir.Example block : settled.examples()) {
            examples.add(HelperNames.qualifyImportsIn(block, self));
        }
        List<Hir.Fake> fakes = new ArrayList<>();
        for (Hir.Fake table : settled.fakes()) {
            fakes.add(HelperNames.qualifyImportsIn(table, self));
        }
        CheckSurface written = new CheckSurface(settling, declarations, fns, examples, fakes,
                List.of(), Map.of());
        // What each row operand computes, emitted beside the module's own so a row runs its operand
        // in the program the behavior it is about is applied in. Which method is whose is kept with
        // the assembly: it is decided here and read wherever a row is run, never counted out again.
        RowFixtures.Emitted rows = RowFixtures.emitted(written.module(), scope, signatures);
        return rows.defs().isEmpty() ? written
                : new CheckSurface(settling, declarations, fns, examples, fakes,
                        List.copyOf(rows.defs().values()), rows.methods());
    }

    /** What the module is called. */
    public String name() {
        return settling.name();
    }

    /** The settling the parts were joined over — the state and not its tree, so that what a caller
     *  compares this against is what a settling answered rather than half of it. */
    InvariantSettled settling() {
        return settling;
    }

    /** The declarations joined here, as the one producer of that form answered for them. */
    List<Normalized.Def> declarations() {
        return declarations;
    }

    /** The behaviors it declares, which no rung at or below this rewrites. */
    public List<Hir.BehaviorDef> behaviors() {
        return settling.module().behaviors();
    }

    /** The names it exposes. */
    public List<String> exposing() {
        return settling.module().exposing();
    }

    /** Whether {@code behavior}'s body is written here as a {@code let} of its own name, which a
     *  composition's is not. Read from the declarations, so it answers whether or not this module
     *  was elaborated. */
    public boolean writesItsOwnBody(Hir.BehaviorDef behavior) {
        return Requirements.writesItsOwnBody(module(), behavior);
    }

    /** Where {@code behavior}'s body comes from. How the behavior is written, which is a question
     *  about the source and not about what a compile made of it. */
    public BehaviorImplementation implementationOf(Hir.BehaviorDef behavior) {
        return Requirements.implementationOf(module(), behavior);
    }


    /** Its definitions, as they came out. */
    public List<Desugared.Fn> fns() {
        return fns;
    }

    /** Its example blocks, written with their imported names spelled out. */
    public List<Hir.Example> examples() {
        return examples;
    }

    /** And its fake tables. */
    public List<Hir.Fake> fakes() {
        return fakes;
    }

    /** The definitions minted for this module's row operands, in the order they were emitted. */
    public List<Hir.FnDef> rowDefs() {
        return rowDefs;
    }

    /** Which method each row operand's value runs as, by the operand. */
    public Map<Hir.Expr, String> operandMethods() {
        return operandMethods;
    }

    /** Which module each imported name was written out to. */
    public Map<String, String> importedFrom() {
        Map<String, String> from = new LinkedHashMap<>();
        for (Hir.Import imp : settling.module().imports()) {
            for (String name : imp.names()) {
                from.put(name, imp.module());
            }
        }
        return from;
    }

    /**
     * The parts written back into the shape a pass over a whole module takes.
     *
     * <p>Built in one place and never read back into parts. This is where the module leaves the
     * assembly: what reads it is handed a tree carrying no proposition, which is why nothing that
     * takes one is a rung.
     */
    public Hir.Module module() {
        Hir.Module built = projected;
        if (built != null) {
            return built;
        }
        List<Hir.FnDef> definitions = new ArrayList<>();
        for (Desugared.Fn fn : fns) {
            definitions.add(fn.read());
        }
        List<Hir.Def> nodes = new ArrayList<>();
        for (Normalized.Def declared : declarations) {
            nodes.add(declared.node());
        }
        projected = built = settling.module().withDefs(nodes).withFns(definitions)
                .withExamples(examples).withFakes(fakes);
        return built;
    }

    @Override
    public boolean equals(Object o) {
        return o instanceof CheckSurface other && module().equals(other.module())
                && rowDefs.equals(other.rowDefs);
    }

    @Override
    public int hashCode() {
        return module().hashCode();
    }
}
