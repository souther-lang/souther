package souther.compiler.check;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BindingOwner;
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
    private final BindingOwner mine;
    private final Substitution enclosing;

    /** The decisions of one application, and of the applications it stands inside. A variable
     * belongs to the application that instantiated it, so a reading of one this expansion did not
     * make is recorded where it belongs rather than shadowed here. */
    Substitution(BindingOwner mine, Substitution enclosing) {
        this.mine = mine;
        this.enclosing = enclosing;
    }

    Substitution() {
        this(null, null);
    }

    /** Where a reading of {@code m} belongs: here, or the enclosing application that instantiated it. */
    private Substitution owning(Type.MetaVar m) {
        if (mine == null || m.application().equals(mine) || enclosing == null) {
            return this;
        }
        return enclosing.owning(m);
    }

    private Type at(Type.MetaVar m) {
        Type here = decided.get(m);
        return here != null || enclosing == null ? here : enclosing.at(m);
    }

    /**
     * Reads {@code actual} against {@code declared}: records what it says about the variables
     * {@code declared} carries, and holds it to everything {@code declared} states.
     *
     * <p>A variable is a hole, not a licence. {@code List<'a>} says the value is a list and leaves
     * what it holds open; {@code Map<String, 'a>} says it is a map with String keys. So an argument
     * is held to the constructors, the arities and the ground positions of a declared type however
     * many variables stand inside it — and only the positions a variable stands at are free.
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
    void constrain(Type declared, Type actual, Symbols symbols, SourcePos pos, String what) {
        decide(declared, actual, symbols, pos, what);
        hold(declared, actual, symbols, pos, what);
    }

    /**
     * Holds {@code actual} to what {@code declared} states, and records nothing.
     *
     * <p>For evidence read off an argument on its own rather than at what the signature settled: what
     * such a reading says is enough to refuse a value the declaration does not admit, and not enough
     * to decide a variable by. A lambda's parameters read off its own body may be narrower than what
     * the application settles them at, so what its body answers under them is not what this
     * application decided.
     */
    void hold(Type declared, Type actual, Symbols symbols, SourcePos pos, String what) {
        if (fits(actual, declared, symbols)) {
            return;
        }
        Type stated = settle(declared);
        throw CompileException.of(
                Diagnostic.of(null, "check.expects").title("check.type.mismatch.title")
                        .at(pos).args(what, Type.show(stated, actual), Type.show(actual, stated))
                        .diff(Type.show(actual, stated), Type.show(stated, actual)).build(),
                what + " expects " + Type.show(stated) + ", but got " + Type.show(actual));
    }

    /**
     * Whether a value of {@code actual} may stand where {@code declared} was written, reading a
     * position this application has not decided as one that states nothing. Everything around it
     * still states what it states.
     *
     * <p>Every position is asked on its own. There is no test for whether the type holds a hole
     * somewhere before descending into it, because that is the question this is: a hole is one
     * position, and asking about the type as a whole is what would let one silence the rest.
     */
    private boolean fits(Type actual, Type declared, Symbols symbols) {
        Type want = zonk(declared);
        // A position states nothing where a variable stands at it — one this application has not
        // decided, or one a declaration wrote, which stands for whatever each use of it makes — and
        // where it stands at what an empty collection carries, which is a reading so far and is
        // widened by a later one (ADR-0028). Nothing is refused at any of them, and everything
        // around them is read.
        if (want instanceof Type.Open || want instanceof Type.Nothing
                || actual instanceof Type.Open) {
            return true;
        }
        if (actual instanceof Type.Nothing || actual instanceof Type.Never
                || actual instanceof Type.Erroneous) {
            return true;   // nothing arrives from there, so nothing of the wrong shape can
        }
        return switch (want) {
            case Type.ListOf l -> actual instanceof Type.ListOf a
                    && fits(a.element(), l.element(), symbols);
            case Type.SetOf s -> actual instanceof Type.SetOf a
                    && fits(a.element(), s.element(), symbols);
            case Type.OptionOf o -> actual instanceof Type.OptionOf a
                    && fits(a.element(), o.element(), symbols);
            case Type.MapOf m -> actual instanceof Type.MapOf a
                    && fits(a.key(), m.key(), symbols) && fits(a.value(), m.value(), symbols);
            case Type.TupleOf t -> actual instanceof Type.TupleOf a
                    && t.elements().size() == a.elements().size()
                    && allFit(a.elements(), t.elements(), symbols);
            case Type.FnOf f -> actual instanceof Type.FnOf a
                    && f.params().size() == a.params().size()
                    && allFit(a.params(), f.params(), symbols)
                    && fits(a.result(), f.result(), symbols);
            // Not a shape with anything inside it to weigh position by position, so what is left is
            // the ordinary question. It answers a variable the declaration wrote too, which is not
            // this application's to decide and stands for whatever each use of it makes it.
            default -> TypeOps.assignable(actual, want, symbols);
        };
    }

    private boolean allFit(List<Type> actual, List<Type> declared, Symbols symbols) {
        for (int i = 0; i < declared.size(); i++) {
            if (!fits(actual.get(i), declared.get(i), symbols)) {
                return false;
            }
        }
        return true;
    }

    /**
     * Records what {@code actual} says about the variables {@code declared} carries, and states
     * nothing about whether the two agree — for a reader that is working out what it holds rather
     * than checking a value against it.
     */
    void decide(Type declared, Type actual, Symbols symbols, SourcePos pos, String what) {
        // Neither side is written through first. A variable already decided is still the variable
        // this reading is about, and writing what it stands for in its place would leave nothing for
        // a later, more definite reading to rebind — which is what a first reading carrying the
        // bottom needs. What it was decided to is {@link #bind}'s to weigh.
        Type left = declared;
        Type right = actual;
        switch (left) {
            case Type.MetaVar m -> bind(m, right, symbols, pos, what);
            case Type.ListOf l when right instanceof Type.ListOf a ->
                    decide(l.element(), a.element(), symbols, pos, what);
            case Type.SetOf s when right instanceof Type.SetOf a ->
                    decide(s.element(), a.element(), symbols, pos, what);
            case Type.OptionOf o when right instanceof Type.OptionOf a ->
                    decide(o.element(), a.element(), symbols, pos, what);
            case Type.MapOf m when right instanceof Type.MapOf a -> {
                decide(m.key(), a.key(), symbols, pos, what);
                decide(m.value(), a.value(), symbols, pos, what);
            }
            case Type.TupleOf t when right instanceof Type.TupleOf a
                    && t.elements().size() == a.elements().size() -> {
                for (int i = 0; i < t.elements().size(); i++) {
                    decide(t.elements().get(i), a.elements().get(i), symbols, pos, what);
                }
            }
            case Type.FnOf f when right instanceof Type.FnOf a
                    && f.params().size() == a.params().size() -> {
                for (int i = 0; i < f.params().size(); i++) {
                    decide(f.params().get(i), a.params().get(i), symbols, pos, what);
                }
                decide(f.result(), a.result(), symbols, pos, what);
            }
            // The other side carries what this one left open: a declared `List<Int>` read against a
            // result still standing at a variable says what that variable is.
            case Type _ when right instanceof Type.MetaVar m -> bind(m, left, symbols, pos, what);
            // Neither side is open, or the shapes do not line up. Either way there is no variable
            // here to decide; whether they agree is {@link #fits}'s question.
            default -> { }
        }
    }

    /** {@code t} with every variable this has decided written into it. One still open is left
     * standing: it is not yet wrong, only not yet answered. */
    Type zonk(Type t) {
        return switch (t) {
            case Type.MetaVar m -> {
                Type at = at(m);
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
        Substitution owner = owning(m);
        Type held = owner.at(m);
        if (held == null || held instanceof Type.Nothing) {
            if (!(at instanceof Type.MetaVar other) || at(other) == null) {
                owner.decided.put(m, at);
            }
            return;
        }
        if (at instanceof Type.Nothing || open(at) || open(held)) {
            return;   // the bottom settles nothing, and neither does a reading still open
        }
        // A reading that carried the bottom said what the value was made of and not what it holds —
        // `Option.withDefault([], xs)` reads the variable as a list of nothing first — so a later
        // reading that says what it holds is what stands. The same rule as widening a bare bottom
        // (ADR-0028), asked at whatever depth the bottom turned up.
        if (Type.mentions(held, x -> x instanceof Type.Nothing)
                && TypeOps.assignable(held, at, symbols)) {
            owner.decided.put(m, at);
            return;
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
