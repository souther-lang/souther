package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

/**
 * What declarations already say about the type of a value expression.
 *
 * <p>One walk. Every consumer that needs the question reads this rather than putting declaration-led
 * typing together again: the reading that builds a row, the pass that decides which methods a row's
 * calls need emitted, the measure that asks what a fixture states, and the editor asking what may be
 * written after a {@code .}. Two walks would be two answers about the same declarations, and the one
 * that answered later would find nothing.
 *
 * <p>How the evidence flows through an expression is this walk's, and what a {@code .} on a value
 * may name is not. Which names a position makes readable, how far the names it wears come off, and
 * what one of those declarations holds under a name are {@link FieldRead}'s — one reading, the same
 * one an elaboration types a text by. So a caller in a world where the check has settled what a
 * value is made of gets that answer here, the walk cannot reach a second one by reading the
 * declaration itself, and a name every case of a sum spreads is answered for because it is
 * readable, rather than left unanswered because a sum lays out no field of its own.
 *
 * <p>Nothing is run. Every step reads a name {@code Resolve} already settled or a declaration a
 * module already made, so asking costs no helper a second application against a row's budget.
 *
 * @param read   the reading of a {@code .}, in the world this walk is being made in — handed over
 *               rather than made here, so which world that is, in both halves of it, is settled by
 *               whoever is doing the reading and not once per walk
 * @param values the definitions a bare name may stand for
 * @param bound  what the bindings in force where the walk starts have to say about themselves, which
 *               the walk adds to as it enters more of them
 */
public record DeclaredTypeEvidence(FieldRead read,
                                   Map<String, Hir.FnDef> values,
                                   Map<BindingId, BindingEvidence> bound) {

    public DeclaredTypeEvidence(FieldRead read, Map<String, Hir.FnDef> values) {
        this(read, values, Map.of());
    }

    /** What the names in a position denote, which is the reading's. One of them and not one here
     *  beside it: two that could differ are two answers about what a name means. */
    public Symbols symbols() {
        return read.symbols();
    }

    /** The same, with {@code binding} standing for {@code value} as well. */
    public DeclaredTypeEvidence with(BindingId binding, Hir.Expr value) {
        Map<BindingId, BindingEvidence> wider = new LinkedHashMap<>(bound);
        wider.put(binding, new BindingEvidence.BoundTo(value));
        return new DeclaredTypeEvidence(read, values, wider);
    }

    /** Bindings that each stand for an expression, as this walk holds them — what a caller keeping
     *  its own record of what a {@code let} put in force hands over. */
    public static Map<BindingId, BindingEvidence> boundTo(Map<BindingId, Hir.Expr> expressions) {
        Map<BindingId, BindingEvidence> out = new LinkedHashMap<>();
        expressions.forEach((binding, value) -> out.put(binding, new BindingEvidence.BoundTo(value)));
        return out;
    }

    /**
     * What {@code e} is declared to be, or null where no declaration says — which is where a helper
     * stands, since what a helper was declared to answer with is not read and what it supplied is
     * its answer's to say.
     *
     * <p>Null is this walk's word for absence, and every caller reads it as that and nothing else:
     * the expression states no type here. A name resolution answered with nothing is one of the
     * ways — it names no declaration to read a type off, and the mistake in it is reported where it
     * is written.
     */
    public Type declaredTypeOf(Hir.Expr e) {
        return declaredTypeOf(e, new HashSet<>(), new HashMap<>(bound));
    }

    /** As above, from a walk that already has names in force and a record of what it has entered. */
    public Type declaredTypeOf(Hir.Expr e, Set<ValueName> seen,
                               Map<BindingId, BindingEvidence> inForce) {
        return switch (e) {
            case Hir.NewData nd -> nd.typeName().answered() == null
                    ? null : Type.ref(nd.typeName().answered().type());
            // `AmountN(100)` is the newtype's construction written in call form (ADR-0032).
            case Hir.Apply c when constructsANewtype(c) -> Type.ref(constructs(c));
            case Hir.FieldAccess fa -> {
                Type target = declaredTypeOf(fa.target(), seen, inForce);
                yield target == null ? null : read.of(target, fa.field());
            }
            case Hir.LetIn let -> {
                BindingId binding = let.binder().id();
                BindingEvidence outer =
                        inForce.put(binding, new BindingEvidence.BoundTo(let.value()));
                try {
                    yield declaredTypeOf(let.body(), seen, inForce);
                } finally {
                    if (outer == null) {
                        inForce.remove(binding);
                    } else {
                        inForce.put(binding, outer);
                    }
                }
            }
            // A name resolution answered with nothing states no type: there is no declaration to
            // read one off, and what is wrong with the name is reported where it is written.
            case Hir.Var v when v.answered() == null -> null;
            case Hir.Var v -> {
                ValueName denotes = v.answered().denotes();
                // A name reached twice is the cycle the reading itself reports; this walk only stops.
                if (!seen.add(denotes)) {
                    yield null;
                }
                if (denotes instanceof ValueName.Local local) {
                    // What the binding says about itself: one more step of this walk where it stands
                    // for an expression, and the answer outright where a declaration gave it one.
                    yield switch (inForce.get(local.id())) {
                        case BindingEvidence.BoundTo(Hir.Expr body) ->
                                declaredTypeOf(body, seen, inForce);
                        case BindingEvidence.DeclaredAs(Type declared) -> declared;
                        case null -> null;
                    };
                }
                Hir.Expr body = valueBody(v.name());
                yield body == null ? null : declaredTypeOf(body, seen, inForce);
            }
            case null, default -> null;
        };
    }

    /**
     * Whether a value of {@code type} is held to a rule its declarations wrote.
     *
     * <p>Every rule that applies to it, and not the ones written on it. A spread flattens the fields
     * of what it brings in and inherits its invariants with them (ADR-0030), so a data that writes
     * no clause of its own is held to whatever it spread in — and a reading that looked at the
     * declaration's own clauses would say a value of it is held to nothing while the compiler
     * refuses one that breaks a rule.
     *
     * <p>Asked of the walk that settles which clauses apply. Following the spreads here would be
     * that walk written again, and the one that forgot a step would disagree with the checker about
     * what a value has to hold.
     */
    public boolean heldToARule(Type type) {
        return type instanceof Type.Ref(TypeSymbol named)
                && symbols().declaredNode(named) instanceof Hir.Data data
                && !TypeOps.settledInvariants(data, symbols()).isEmpty();
    }

    /** The body a name stands for, where it names a value of this reading's own. */
    public Hir.Expr valueBody(String name) {
        Hir.FnDef value = values.get(name);
        return value != null && value.params().isEmpty()
                && value.body() instanceof Hir.FnBody.Written w ? w.expr() : null;
    }

    private boolean isNewtype(TypeSymbol name) {
        return isNewtype(name, symbols());
    }

    /** Whether an application is a newtype's construction written in call form (ADR-0032). */
    private boolean constructsANewtype(Hir.Apply c) {
        TypeSymbol built = constructs(c);
        return built != null && isNewtype(built);
    }

    private static TypeSymbol constructs(Hir.Apply c) {
        return c.answered() != null && c.answered().denotes() instanceof ValueName.OfType named
                ? named.type() : null;
    }

    // --- what a declaration says, asked of the resolution and never of a spelling ------------------

    /**
     * Whether {@code name} is a newtype. Asked of a name resolution settled, never of a spelling: an
     * imported value's body names its own module's types, which the module reading the row need not
     * have imported, and a module of its own may declare something else of that spelling.
     */
    public static boolean isNewtype(TypeSymbol name, Symbols symbols) {
        return name != null
                && symbols.declaredNode(name) instanceof Hir.Data d && d.newtype();
    }

}
