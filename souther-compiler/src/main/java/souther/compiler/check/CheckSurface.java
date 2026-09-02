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
 * <p>Its declaration nodes are nevertheless written in the same declaration-local form the derived
 * stage uses ({@link Derived#normalized}): failing to derive a representation does not put an
 * earlier spelling back into the tree. A module holding one declaration that could not be derived is
 * still read for what its other definitions say, and the declaration that could not be derived is
 * here in the form every reader below the settling expects — not beside them in a spelling one rung
 * up, which nothing in a tree would say was different.
 *
 * <p>Not a rung. What a state of this package says is that something was established of a value;
 * what this says is where the parts were joined. {@link Prepared} is the state — it is this
 * assembly beside the witness that every declaration came out — and a reader that has to have a
 * whole module asks for that one.
 */
public final class CheckSurface {

    private final Hir.Module settled;
    private final List<Hir.Def> declarations;
    private final List<Desugared.Fn> fns;
    private final List<Hir.Example> examples;
    private final List<Hir.Fake> fakes;
    private final List<Hir.FnDef> rowDefs;
    private final Map<Hir.Expr, String> operandMethods;
    /** Worked out once, as the rungs beside this work theirs out. */
    private volatile Hir.Module projected;

    private CheckSurface(Hir.Module settled, List<Hir.Def> declarations, List<Desugared.Fn> fns,
                         List<Hir.Example> examples, List<Hir.Fake> fakes,
                         List<Hir.FnDef> rowDefs, Map<Hir.Expr, String> operandMethods) {
        this.settled = settled;
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
     * <p>The declarations are normalised here rather than handed in, so what is on the surface is
     * what {@link Derived#normalized} answers with for every declaration the module writes and
     * cannot be anything else. {@code desugared} is the definitions that came out, which may be
     * short of what the module wrote: a definition is worked out whether or not the one before it
     * came out.
     *
     * <p>{@code resolved} is the world a declaration is normalised against, which is the world the
     * derived stage normalises against — the same operation over the same names, so a declaration
     * here and the same one on a derived declaration are one node. {@code scope} is what a name
     * means below the derivation, which is what a definition is held to after it is rewritten;
     * {@code signatures} is what each behavior takes and answers with, which says where a row's
     * values stand.
     *
     * @throws CompileException where a declaration cannot be read that way, or a definition cannot
     *     be held to what it was rewritten to
     */
    public static CheckSurface assemble(InvariantSettled settling, ResolvedSymbols resolved,
                                        Map<String, Desugared.Fn> desugared, Symbols scope,
                                        Map<ValueName.Behavior, Sig> signatures) {
        Hir.Module settled = settling.module();
        List<Hir.Def> declarations = new ArrayList<>();
        for (InvariantSettled.Def def : settling.defs()) {
            declarations.add(Derived.normalized(def, resolved));
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
            if (came != null) {
                fns.add(Desugared.Fn.reestablish(
                        HelperNames.qualifyImportsIn(came.read(), self), scope));
            }
        }
        List<Hir.Example> examples = new ArrayList<>();
        for (Hir.Example block : settled.examples()) {
            examples.add(HelperNames.qualifyImportsIn(block, self));
        }
        List<Hir.Fake> fakes = new ArrayList<>();
        for (Hir.Fake table : settled.fakes()) {
            fakes.add(HelperNames.qualifyImportsIn(table, self));
        }
        CheckSurface written = new CheckSurface(settled, declarations, fns, examples, fakes,
                List.of(), Map.of());
        // What each row operand computes, emitted beside the module's own so a row runs its operand
        // in the program the behavior it is about is applied in. Which method is whose is kept with
        // the assembly: it is decided here and read wherever a row is run, never counted out again.
        RowFixtures.Emitted rows = RowFixtures.emitted(written.module(), scope, signatures);
        return rows.defs().isEmpty() ? written
                : new CheckSurface(settled, declarations, fns, examples, fakes,
                        List.copyOf(rows.defs().values()), rows.methods());
    }

    /** What the module is called. */
    public String name() {
        return settled.name();
    }

    /** The behaviors it declares, which no rung at or below this rewrites. */
    public List<Hir.BehaviorDef> behaviors() {
        return settled.behaviors();
    }

    /** The names it exposes. */
    public List<String> exposing() {
        return settled.exposing();
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

    /** Its declarations, each written in the form the derived stage writes one in. */
    public List<Hir.Def> declarations() {
        return declarations;
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
        for (Hir.Import imp : settled.imports()) {
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
        projected = built = settled.withDefs(declarations).withFns(definitions)
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
