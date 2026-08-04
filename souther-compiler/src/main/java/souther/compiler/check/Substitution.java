package souther.compiler.check;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * What one application of a signature has decided about the variables it left open.
 *
 * <p>It belongs to a single {@link souther.compiler.ast.Ast.Expansion} and lives as long as that
 * expansion's elaboration. The signature is instantiated once into {@link Type.MetaVar}s, the
 * arguments say what those stand for, and the result is written back over the whole signature — so
 * what a declaration said between its parameters and its result reaches the caller whether or not
 * the expansion left a fragment carrying it.
 *
 * <p>Keyed by the variable itself, not by its spelling. A {@link Type.MetaVar} is the pair of the
 * application and the variable that application's callee wrote, so two calls of one signature are two
 * keys without any name being made unique by hand.
 */
final class Substitution {

    private final Map<Type.MetaVar, Type> decided = new LinkedHashMap<>();

    /**
     * Reads {@code actual} against {@code declared} and records what that says about the variables
     * {@code declared} carries.
     *
     * <p>A variable takes the first type it is read at, and every later reading must agree. The
     * empty-collection bottom is the one exception, in both directions: it settles nothing, so a
     * variable standing at the bottom is widened by a later concrete reading and a bottom reading
     * leaves a concrete one alone (ADR-0028). That is what lets an empty seed take its element type
     * from the argument that decided it rather than from itself.
     *
     * <p>A disagreement is the caller's error and is reported here, at {@code pos}. It is not
     * swallowed on the grounds that another pass would report it too: what this holds is the whole
     * signature at once, so it is the only reader that can see two positions of one variable
     * disagree.
     */
    void unify(Type declared, Type actual, Symbols symbols, SourcePos pos, String what) {
        Type left = zonk(declared);
        Type right = zonk(actual);
        switch (left) {
            case Type.MetaVar m -> bind(m, right, symbols, pos, what);
            case Type.ListOf l when right instanceof Type.ListOf a ->
                    unify(l.element(), a.element(), symbols, pos, what);
            case Type.SetOf s when right instanceof Type.SetOf a ->
                    unify(s.element(), a.element(), symbols, pos, what);
            case Type.OptionOf o when right instanceof Type.OptionOf a ->
                    unify(o.element(), a.element(), symbols, pos, what);
            case Type.MapOf m when right instanceof Type.MapOf a -> {
                unify(m.key(), a.key(), symbols, pos, what);
                unify(m.value(), a.value(), symbols, pos, what);
            }
            case Type.TupleOf t when right instanceof Type.TupleOf a
                    && t.elements().size() == a.elements().size() -> {
                for (int i = 0; i < t.elements().size(); i++) {
                    unify(t.elements().get(i), a.elements().get(i), symbols, pos, what);
                }
            }
            case Type.FnOf f when right instanceof Type.FnOf a
                    && f.params().size() == a.params().size() -> {
                for (int i = 0; i < f.params().size(); i++) {
                    unify(f.params().get(i), a.params().get(i), symbols, pos, what);
                }
                unify(f.result(), a.result(), symbols, pos, what);
            }
            // The other side carries what this one left open: a declared `List<Int>` read against a
            // result still standing at a variable says what that variable is.
            case Type _ when right instanceof Type.MetaVar m -> bind(m, left, symbols, pos, what);
            // Neither side is open. Whether they agree is an ordinary question about ground types,
            // and the answer belongs to whoever asked for this reading.
            default -> { }
        }
    }

    /** {@code t} with every variable this has decided written into it. One still open is left
     * standing: it is not yet wrong, only not yet answered. */
    Type zonk(Type t) {
        return switch (t) {
            case Type.MetaVar m -> {
                Type at = decided.get(m);
                yield at == null ? m : zonk(at);
            }
            case Type.ListOf l -> Type.list(zonk(l.element()));
            case Type.SetOf s -> Type.set(zonk(s.element()));
            case Type.OptionOf o -> Type.option(zonk(o.element()));
            case Type.MapOf m -> Type.map(zonk(m.key()), zonk(m.value()));
            case Type.TupleOf tu -> {
                List<Type> es = new ArrayList<>();
                for (Type e : tu.elements()) {
                    es.add(zonk(e));
                }
                yield Type.tuple(es);
            }
            case Type.FnOf f -> {
                List<Type> ps = new ArrayList<>();
                for (Type p : f.params()) {
                    ps.add(zonk(p));
                }
                yield Type.fn(ps, zonk(f.result()));
            }
            default -> t;
        };
    }

    /**
     * {@code t} as it leaves the expansion: decided where the application decided, and read as the
     * empty-collection bottom where it did not.
     *
     * <p>A variable nothing pinned is in the same position as the element of {@code []}, and takes
     * the same answer (ADR-0028) — not the annotation being thrown away, which would lose the
     * constructor and the arguments that <em>were</em> decided. {@code Map<String, _>} still says the
     * result is a map with {@code String} keys.
     *
     * <p>Nothing below elaboration ever sees a {@link Type.MetaVar}, because everything the
     * expansion hands out goes through here.
     */
    Type settle(Type t) {
        Type at = zonk(t);
        return Type.mentions(at, x -> x instanceof Type.MetaVar) ? toBottom(at) : at;
    }

    /** Whether {@code t} still holds a variable this application has not decided. */
    boolean open(Type t) {
        return Type.mentions(zonk(t), x -> x instanceof Type.MetaVar);
    }

    private void bind(Type.MetaVar m, Type at, Symbols symbols, SourcePos pos, String what) {
        if (at == m || Type.mentions(at, m::equals)) {
            // A variable cannot stand for something it stands inside: a list of itself is a value
            // that would have to hold itself. It stays open, and the reading that said so settles
            // nothing rather than being taken as a disagreement — the same answer {@link Readings}
            // gives the same question.
            return;
        }
        Type held = decided.get(m);
        if (held == null || held instanceof Type.Nothing) {
            if (!(at instanceof Type.MetaVar other) || decided.get(other) == null) {
                decided.put(m, at);
            }
            return;
        }
        if (at instanceof Type.Nothing || open(at) || open(held)) {
            return;   // the bottom settles nothing, and neither does a reading still open
        }
        if (TypeOps.assignable(at, held, symbols) || TypeOps.assignable(held, at, symbols)) {
            return;
        }
        throw CompileException.of(
                Diagnostic.of(null, "check.generic.arg").title("check.type.mismatch.title")
                        .at(pos).args(what, Type.show(held, at), Type.show(at, held))
                        .diff(Type.show(at, held), Type.show(held, at)).build(),
                what + ": expected " + Type.show(held) + " but got " + Type.show(at));
    }

    /** Every variable still open read as the bottom, at every depth. */
    private Type toBottom(Type t) {
        return switch (t) {
            case Type.MetaVar _ -> Type.NOTHING;
            case Type.ListOf l -> Type.list(toBottom(l.element()));
            case Type.SetOf s -> Type.set(toBottom(s.element()));
            case Type.OptionOf o -> Type.option(toBottom(o.element()));
            case Type.MapOf m -> Type.map(toBottom(m.key()), toBottom(m.value()));
            case Type.TupleOf tu -> {
                List<Type> es = new ArrayList<>();
                for (Type e : tu.elements()) {
                    es.add(toBottom(e));
                }
                yield Type.tuple(es);
            }
            case Type.FnOf f -> {
                List<Type> ps = new ArrayList<>();
                for (Type p : f.params()) {
                    ps.add(toBottom(p));
                }
                yield Type.fn(ps, toBottom(f.result()));
            }
            default -> t;
        };
    }
}
