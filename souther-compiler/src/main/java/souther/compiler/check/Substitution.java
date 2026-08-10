package souther.compiler.check;

import souther.compiler.types.BindingOwner;
import souther.compiler.types.Type;

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
     * Holds {@code actual} to what {@code declared} states, and records nothing.
     *
     * <p>For evidence read off an argument on its own rather than at what the signature settled: what
     * such a reading says is enough to refuse a value the declaration does not admit, and not enough
     * to decide a variable by. A lambda's parameters read off its own body may be narrower than what
     * the application settles them at, so what its body answers under them is not what this
     * application decided.
     */
    Fit hold(Type declared, Type actual, Symbols symbols) {
        return fits(actual, declared, symbols)
                ? Fit.FITS : new Fit.Disagrees(settle(declared), actual);
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
    private boolean fits(Type is, Type declared, Symbols symbols) {
        Type want = zonk(declared);
        Type actual = zonk(is);
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
            // Nothing inside it to weigh position by position, so what is left is the ordinary
            // question. It answers a variable the declaration wrote too, which is not this
            // application's to decide and stands for whatever each use of it makes it.
            case Type.Leaf _ -> TypeOps.assignable(actual, want, symbols);
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
     * nothing about whether the two shapes agree — for a reader that is working out what it holds
     * rather than checking a value against it. That question is {@link #hold}'s.
     *
     * <p>What it does answer is a variable this application has already read at a type that does not
     * go with this one: two readings of one variable, which is the one disagreement only a reader
     * holding the whole signature can see. The types are answered rather than reported, because
     * where a reader is sent belongs to whoever still has the operand.
     *
     * <p>A reading that disagrees leaves behind what it decided before it got there. Unlike
     * {@link TypeOps#unify}, which settles a caller's map and so has to leave it as the caller left
     * it, this settles what the application already owns: what a walk decides is the application's
     * decision from the moment it is made, and a reading that turned out to disagree does not
     * un-decide the positions before it. So a caller that goes on after {@code Disagrees} is
     * carrying an application whose readings did not all agree, which is not something to build a
     * type from. Every caller today either refuses at once or drops the whole {@code Substitution},
     * and a caller that wants to do neither is asking for something this does not offer.
     */
    Fit decide(Type declared, Type actual, Symbols symbols) {
        // Neither side is written through first. A variable already decided is still the variable
        // this reading is about, and writing what it stands for in its place would leave nothing for
        // a later, more definite reading to rebind — which is what a first reading carrying the
        // bottom needs. What it was decided to is {@link #bind}'s to weigh.
        Type left = declared;
        Type right = actual;
        if (left instanceof Type.MetaVar m) {
            return bind(m, right, symbols);
        }
        // The other side carries what this one left open: a declared `List<Int>` read against a
        // result still standing at a variable says what that variable is.
        if (right instanceof Type.MetaVar m) {
            return bind(m, left, symbols);
        }
        // Position by position where the two shapes line up. Where they do not there is no variable
        // here to decide, and whether they agree is {@link #fits}'s question.
        switch (left) {
            case Type.ListOf l -> {
                if (right instanceof Type.ListOf a) {
                    return decide(l.element(), a.element(), symbols);
                }
            }
            case Type.SetOf s -> {
                if (right instanceof Type.SetOf a) {
                    return decide(s.element(), a.element(), symbols);
                }
            }
            case Type.OptionOf o -> {
                if (right instanceof Type.OptionOf a) {
                    return decide(o.element(), a.element(), symbols);
                }
            }
            case Type.MapOf m -> {
                if (right instanceof Type.MapOf a) {
                    Fit key = decide(m.key(), a.key(), symbols);
                    return key instanceof Fit.Disagrees ? key : decide(m.value(), a.value(), symbols);
                }
            }
            case Type.TupleOf t -> {
                if (right instanceof Type.TupleOf a
                        && t.elements().size() == a.elements().size()) {
                    for (int i = 0; i < t.elements().size(); i++) {
                        Fit at = decide(t.elements().get(i), a.elements().get(i), symbols);
                        if (at instanceof Fit.Disagrees) {
                            return at;
                        }
                    }
                }
            }
            case Type.FnOf f -> {
                if (right instanceof Type.FnOf a && f.params().size() == a.params().size()) {
                    for (int i = 0; i < f.params().size(); i++) {
                        Fit at = decide(f.params().get(i), a.params().get(i), symbols);
                        if (at instanceof Fit.Disagrees) {
                            return at;
                        }
                    }
                    return decide(f.result(), a.result(), symbols);
                }
            }
            // Nothing inside it to descend into, so nothing here decides a variable.
            case Type.Leaf _ -> { }
        }
        return Fit.FITS;
    }

    /** {@code t} with every variable this has decided written into it. One still open is left
     * standing: it is not yet wrong, only not yet answered. */
    Type zonk(Type t) {
        if (t instanceof Type.MetaVar m) {
            Type at = at(m);
            return at == null ? m : zonk(at);
        }
        return Type.mapChildren(t, this::zonk);
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

    private Fit bind(Type.MetaVar m, Type reading, Symbols symbols) {
        // What the reading stands for, not how it was written. A variable another application
        // decided is that decision here, and comparing the variable itself would find every reading
        // through one to disagree with every other.
        Type at = zonk(reading);
        if (at == m || Type.mentions(at, m::equals)) {
            // A variable cannot stand for something it stands inside: a list of itself is a value
            // that would have to hold itself. It stays open, and the reading that said so settles
            // nothing rather than being taken as a disagreement — the same answer {@link Readings}
            // gives the same question.
            return Fit.FITS;
        }
        Substitution owner = owning(m);
        Type held = owner.at(m);
        if (held == null || held instanceof Type.Nothing) {
            if (!(at instanceof Type.MetaVar other) || at(other) == null) {
                owner.decided.put(m, at);
            }
            return Fit.FITS;
        }
        if (at instanceof Type.Nothing || open(at) || open(held)) {
            return Fit.FITS;   // the bottom settles nothing, and neither does a reading still open
        }
        // A reading that carried the bottom said what the value was made of and not what it holds —
        // `Option.withDefault([], xs)` reads the variable as a list of nothing first — so a later
        // reading that says what it holds is what stands. The same rule as widening a bare bottom
        // (ADR-0028), asked at whatever depth the bottom turned up.
        if (Type.mentions(held, x -> x instanceof Type.Nothing)
                && TypeOps.assignable(held, at, symbols)) {
            owner.decided.put(m, at);
            return Fit.FITS;
        }
        Type stands = zonk(held);
        if (TypeOps.assignable(at, stands, symbols) || TypeOps.assignable(stands, at, symbols)) {
            return Fit.FITS;
        }
        return new Fit.Disagrees(held, at);
    }

    /** Every variable still open read as the bottom, at every depth. */
    private Type toBottom(Type t) {
        return t instanceof Type.MetaVar ? Type.NOTHING : Type.mapChildren(t, this::toBottom);
    }
}
