package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Predicate;

/**
 * How a definition is named outside the module that declares it, and what a body carries out of the
 * module it was written in.
 *
 * <p>A reader writes an imported value or helper bare, and the pair (module, name) is what it
 * denotes. Writing the qualified spelling into the tree settles the name a reader reaches it by, so
 * everything downstream — the table a call is expanded against, the method a recursive helper is
 * emitted as — asks and answers with one name, and two modules publishing a {@code tally} stay two
 * entries. Every rewrite here reads what a name denotes and never how it was spelled, so running one
 * twice says what running it once said.
 *
 * <p>What that spelling settles is the reach name, and it is not the declaration's identity. The two
 * coincide for a helper another module published and part ways for the standard library, which is
 * reached under an alias: {@code List.foldFrom} is declared in {@code souther.list}, and no reader of
 * the name can get there from it. Which module declared a definition is carried on the declaration
 * ({@link Ast.FnDef#declaredIn}), and every rule about the declaring module reads it there.
 *
 * <p>The marks a construction carries belong here for the same reason. What a published body builds
 * is built where that body was written; expanding it puts the construction in the reader's body,
 * where nothing left in the tree would say otherwise. The mark is what says so, and it is written
 * where the name is.
 *
 * <p>Nothing here reads a helper table or writes a binding: these are questions about names, and the
 * answers are the same whichever module is asking.
 */
public final class HelperNames {

    private HelperNames() {}

    /** How a definition of {@code module} is named outside it. */
    public static String qualified(String module, String name) {
        return module + "." + name;
    }

    /**
     * {@code m} with every name that denotes another module's definition written qualified.
     *
     * <p>Done once, here, because the spelling travels as far as the emitted method name; deciding it
     * at each reader is how one of them comes to disagree.
     */
    public static Ast.Module qualifyImports(Ast.Module m) {
        List<Ast.FnDef> fns = new ArrayList<>();
        for (Ast.FnDef fn : m.fns()) {
            fns.add(fn.body() instanceof Ast.FnBody.Written w
                    ? fn.withBody(new Ast.FnBody.Written(qualifyForeign(w.expr(), m.name())))
                    : fn);
        }
        List<Ast.Def> defs = qualifiedInvariants(m);
        List<Ast.Example> examples = new ArrayList<>();
        for (Ast.Example ex : m.examples()) {
            List<Ast.ExampleRow> rows = new ArrayList<>();
            for (Ast.ExampleRow row : ex.rows()) {
                List<Ast.Expr> inputs = new ArrayList<>();
                for (Ast.Expr in : row.inputs()) {
                    inputs.add(qualifyForeign(in, m.name()));
                }
                List<Ast.With> withs = new ArrayList<>();
                for (Ast.With w : row.withs()) {
                    withs.add(new Ast.With(w.dep(), qualifyForeign(w.value(), m.name()), w.pos()));
                }
                rows.add(new Ast.ExampleRow(row.description(), inputs, withs,
                        qualifyForeign(row.expected(), m.name()), row.pos()));
            }
            examples.add(new Ast.Example(ex.target(), rows, ex.pos()));
        }
        List<Ast.Fake> fakes = new ArrayList<>();
        for (Ast.Fake fake : m.fakes()) {
            List<Ast.FakeRow> rows = new ArrayList<>();
            for (Ast.FakeRow row : fake.rows()) {
                List<Ast.Expr> inputs = null;
                if (row.inputs() != null) {   // a default row matches anything and writes none
                    inputs = new ArrayList<>();
                    for (Ast.Expr in : row.inputs()) {
                        inputs.add(qualifyForeign(in, m.name()));
                    }
                }
                rows.add(new Ast.FakeRow(inputs, qualifyForeign(row.output(), m.name()),
                        row.isDefault(), row.pos()));
            }
            fakes.add(new Ast.Fake(fake.target(), rows, fake.pos()));
        }
        return new Ast.Module(m.name(), m.exposing(), m.exposedOutputs(), m.imports(), defs,
                m.behaviors(), fns, examples, fakes, m.exampleFileTarget(), m.pos());
    }

    /** {@code m} with the foreign names in its invariants written qualified, and nothing else
     * changed. An invariant is read before the bodies are — settled here, classified for discharge
     * there — so this is the part of {@link #qualifyImports} that has to be available on its own. */
    public static Ast.Module withQualifiedInvariants(Ast.Module m) {
        List<Ast.Def> defs = qualifiedInvariants(m);
        return defs.equals(m.defs()) ? m
                : new Ast.Module(m.name(), m.exposing(), m.exposedOutputs(), m.imports(), defs,
                        m.behaviors(), m.fns(), m.examples(), m.fakes(), m.exampleFileTarget(),
                        m.pos());
    }

    /** {@code m}'s declarations with every name in an invariant that denotes another module's
     * definition written qualified. */
    private static List<Ast.Def> qualifiedInvariants(Ast.Module m) {
        List<Ast.Def> defs = new ArrayList<>();
        for (Ast.Def def : m.defs()) {
            defs.add(def instanceof Ast.Data d && !d.invariants().isEmpty()
                    ? new Ast.Data(d.written(), d.newtype(), d.includes(), d.fields(),
                            Ast.mapClauses(d.invariants(), inv -> qualifyForeign(inv, m.name())),
                            d.decoder(), d.encoder(), d.pos())
                    : def);
        }
        return defs;
    }

    /** {@code e} with every name denoting a helper of a module other than {@code self} written
     * qualified. */
    private static Ast.Expr qualifyForeign(Ast.Expr e, String self) {
        return qualifyHelpers(e, helper -> !helper.module().equals(self));
    }

    /** {@code e} with every name still denoting a helper of {@code module} written qualified. Only a
     * recursive helper survives closing, so this is what those calls become. */
    static Ast.Expr qualifyHelpersOf(Ast.Expr e, String module) {
        return qualifyHelpers(e, helper -> helper.module().equals(module));
    }

    /**
     * {@code e} with every name denoting a helper {@code which} accepts written qualified.
     *
     * <p>It reads what a name denotes rather than how it is spelled: a binding of the same spelling is
     * a binding, and a prelude helper belongs to the prelude and keeps the qualified name it already
     * has. The new spelling is read off the same answer, so running this twice says what running it
     * once said.
     */
    private static Ast.Expr qualifyHelpers(Ast.Expr e, Predicate<ValueName.Helper> which) {
        // a name slot takes the same rewrite as a name standing on its own: a spread names a value
        // the way any other position does
        Ast.Expr rebuilt = Ast.mapChildren(e, c -> qualifyHelpers(c, which),
                s -> qualified(s, which));
        return switch (rebuilt) {
            case Ast.Apply call when foreign(call.denotes(), which) ->
                    new Ast.Apply(qualifiedName(call.denotes()), call.denotes(), call.args(),
                            call.origin(),
                            call.pos());
            case Ast.Var v -> qualified(v, which);
            default -> rebuilt;
        };
    }

    /** {@code name} written qualified where it denotes a helper {@code which} accepts. */
    private static Ast.Var qualified(Ast.Var name, Predicate<ValueName.Helper> which) {
        return foreign(name.denotes(), which)
                ? new Ast.Var(qualifiedName(name.denotes()), name.denotes(), name.pos())
                : name;
    }

    /** Whether {@code denotes} is a helper {@code which} accepts. */
    private static boolean foreign(ValueName denotes, Predicate<ValueName.Helper> which) {
        return denotes instanceof ValueName.Helper helper && which.test(helper);
    }

    /**
     * {@code e} with every construction in it marked as {@code module}'s.
     *
     * <p>What a published body builds is built where that body was written, and the reader is handed
     * the result. Expanding it puts the construction in the reader's body, where the permission check
     * would ask the reader to declare it — for a type the declaring module may keep to itself, under a
     * name the reader has none of. The mark is what tells the two apart afterwards, and it names the
     * module rather than saying only that the construction came from somewhere: a body may build a
     * type of a third module, and that one is nobody's to hand over (ADR-0059).
     */
    static Ast.Expr publishedBy(Ast.Expr e, String module) {
        // a spread names a value, and a value is not a construction: what it built was built where it
        // was defined, so the mark is already on it
        Ast.Expr rebuilt = Ast.mapChildren(e, c -> publishedBy(c, module), s -> s);
        return switch (rebuilt) {
            case Ast.NewData nd -> nd.publishedBy(module);
            // a unit data is constructed by being named, so the name is where it says where it came
            // from — there is no construction node to say it on
            case Ast.Var v when v.denotes() instanceof ValueName.OfType named ->
                    v.denoting(named.publishedBy(module));
            default -> rebuilt;
        };
    }

    /**
     * {@code e} with every construction in it marked as one a value made.
     *
     * <p>A value is substituted at each reference, so what its definition built ends up standing in
     * the body that named it, as the node that body's own construction would be. The mark is what
     * keeps the permission check reading the model rather than the substitution: a behavior stating a
     * rule against a named limit compares against a value, and originates none of it. A limit is
     * written as a value so that the figure has one place to live and one comment saying where it
     * comes from, and naming it is not supposed to cost every rule that reads it an authority it does
     * not use.
     *
     * <p>Unlike a published body's mark this names no module. What the value built is the value
     * definition's however the type got its declaration, and a behavior reading the name is not the
     * one that made it either way. A helper is the other case and stays the other case: its body is
     * checked as though it had been written inline, which is what tells a helper from a behavior.
     *
     * <p>Three things can stand for a construction and each takes the mark. A construction node
     * carries its own; a unit data is constructed by being named, so the name carries it; and a
     * recursive helper is lowered to a method rather than expanded, so what it builds stays behind a
     * call, and the call carries it. Without the third, whether a value's constructions belonged to
     * the value would turn on whether a helper on the way could be expanded — the substitution
     * showing through the rule again, in the one place expansion cannot reach.
     */
    static Ast.Expr carriedByValue(Ast.Expr e) {
        Ast.Expr rebuilt = Ast.mapChildren(e, HelperNames::carriedByValue, s -> s);
        return switch (rebuilt) {
            case Ast.NewData nd -> nd.carriedByValue();
            case Ast.Var v when v.denotes() instanceof ValueName.OfType named ->
                    v.denoting(named.carriedByValue());
            case Ast.Apply call -> call.carriedByValue();
            default -> rebuilt;
        };
    }

    /**
     * The helpers {@code e} still reaches — what a body closed by
     * {@link HelperInliner#closeAcross} could not expand away, which is the recursive ones.
     *
     * <p>Each is given as what it denotes rather than as a spelling, because the two questions a
     * caller then has differ: which module declares it decides how it is keyed, and a binding that
     * shares a helper's spelling is not one of these at all.
     */
    public static Set<ValueName.Helper> helpersReached(Ast.Expr e) {
        Set<ValueName.Helper> out = new LinkedHashSet<>();
        collectHelpersOf(e, out);
        return out;
    }

    private static void collectHelpersOf(Ast.Expr e, Set<ValueName.Helper> out) {
        if (e == null) {
            return;
        }
        ValueName denotes = switch (e) {
            case Ast.Apply call -> call.denotes();
            case Ast.Var v -> v.denotes();
            default -> null;
        };
        if (denotes instanceof ValueName.Helper helper) {
            out.add(helper);
        }
        Ast.forEachChild(e, c -> collectHelpersOf(c, out));
    }

    /** The name a helper is reached by outside the module that declares it. Read off what the name
     * denotes, so applying it to a name already written this way answers the same thing. */
    private static String qualifiedName(ValueName denotes) {
        ValueName.Helper helper = (ValueName.Helper) denotes;
        return qualified(helper.module(), helper.name());
    }

    /**
     * The key {@code helper} is filed under in the table of the module named {@code module} — bare for
     * one that module declares, declaring-module-qualified for one it imported.
     *
     * <p>This turns a helper's identity into the name that module reaches it by, and the two are
     * different values. What comes back is a key: it names a declaration within one module's table and
     * says nothing outside it, and it is not something to read a declaring module back out of. That is
     * carried on the declaration ({@link Ast.FnDef#declaredBy}).
     *
     * <p>Asked with the identity and never with a spelling, which is what {@link ValueName.Helper}
     * holds (ADR-0072); a reader writes an imported definition bare, so a key taken off the spelling
     * would be one key before {@link #qualifyImports} and another after — silently, because a miss is
     * what a table does with a key it has not got.
     *
     * <p>The library does not come through here. A standard-library name is reached under an alias
     * rather than under the module that declares it — {@code souther.list}'s {@code foldFrom} is
     * reached as {@code List.foldFrom} — and denotes a {@link ValueName.Stdlib}, which already holds
     * that reach name and is read as it stands.
     */
    public static String keyIn(String module, ValueName.Helper helper) {
        return helper.module().equals(module) ? helper.name() : qualified(helper.module(), helper.name());
    }
}
