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
 * <p>Nothing is run. Every step reads a name {@code Resolve} already settled or a declaration a
 * module already made, so asking costs no helper a second application against a row's budget.
 *
 * @param values the definitions a bare name may stand for
 * @param bound  what the bindings in force where the walk starts have to say about themselves, which
 *               the walk adds to as it enters more of them
 */
public record DeclaredTypeEvidence(Symbols symbols, Map<String, Hir.FnDef> values,
                                   Map<BindingId, BindingEvidence> bound) {

    public DeclaredTypeEvidence(Symbols symbols, Map<String, Hir.FnDef> values) {
        this(symbols, values, Map.of());
    }

    /** The same, with {@code binding} standing for {@code value} as well. */
    public DeclaredTypeEvidence with(BindingId binding, Hir.Expr value) {
        Map<BindingId, BindingEvidence> wider = new LinkedHashMap<>(bound);
        wider.put(binding, new BindingEvidence.BoundTo(value));
        return new DeclaredTypeEvidence(symbols, values, wider);
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
                yield target == null ? null : fieldTypeOf(target, fa.field());
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
     * The type a field is declared to be, one step. Both the walk that answers what a projection
     * states and the reading that takes the field go through this, so the two cannot come to
     * different answers about which field of what is being read.
     */
    public Type fieldTypeOf(Type record, String field) {
        return fieldsOf(record).get(field);
    }

    /**
     * Every field a value of {@code record} has, in the order its declaration lays them out.
     *
     * <p>Which fields a type has is said here and asked here. A reader after one of them and a
     * reader listing them for an author are asking the same question, and answering it in two places
     * would be two accounts of what a declaration wrote — the one that forgot a rule would forget it
     * for whoever read it.
     *
     * <p>Empty for anything that is not a declared data type. A list has no fields to take, and
     * neither has a type this reading's module cannot see.
     */
    public Map<String, Type> fieldsOf(Type record) {
        if (!(record instanceof Type.Ref r)) {
            return Map.of();
        }
        TypeSymbol named = r.name();
        if (isNewtype(named)) {
            // A newtype declares one field, and it is what it wraps (ADR-0032).
            Type wraps = shapeOf(newtypeBaseType(named, symbols));
            return wraps == null ? Map.of() : Map.of(NEWTYPE_FIELD, wraps);
        }
        Map<String, Type> out = new LinkedHashMap<>();
        fieldTypes(named, symbols).forEach((field, written) -> {
            Type is = shapeOf(written);
            if (is != null) {
                out.put(field, is);
            }
        });
        return out;
    }

    /** What a newtype's one field is called (ADR-0032). */
    private static final String NEWTYPE_FIELD = "value";

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
                && symbols.declarations().declaration(named) instanceof Hir.Data data
                && !TypeOps.effectiveInvariants(data, symbols).isEmpty();
    }

    /** The body a name stands for, where it names a value of this reading's own. */
    public Hir.Expr valueBody(String name) {
        Hir.FnDef value = values.get(name);
        return value != null && value.params().isEmpty()
                && value.body() instanceof Hir.FnBody.Written w ? w.expr() : null;
    }

    private boolean isNewtype(TypeSymbol name) {
        return isNewtype(name, symbols);
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
                && symbols.declarations().declaration(name) instanceof Hir.Data d && d.newtype();
    }

    /** The written form of what a newtype wraps, kept whole so a generic base
     *  ({@code data 在庫 = Map<商品ID, Int>}) keeps its type arguments. */
    public static Hir.TypeRef newtypeBaseType(TypeSymbol name, Symbols symbols) {
        return name != null
                && symbols.declarations().declaration(name) instanceof Hir.Data d && d.newtype()
                && d.fields().size() == 1 && d.fields().get(0).type() instanceof Hir.TypeRef base
                ? base : null;
    }

    /** A data's fields by name, following the {@code ...includes} it composes in (spec §data). */
    public static Map<String, Hir.TypeRef> fieldTypes(TypeSymbol typeName, Symbols symbols) {
        Map<String, Hir.TypeRef> out = new LinkedHashMap<>();
        if (symbols.declarations().declaration(typeName) instanceof Hir.Data d) {
            for (Hir.Name inc : d.includes()) {
                // A spread naming nothing brings in no fields; it is reported where it is written.
                if (inc.answered() instanceof Hir.Name.Denoting named) {
                    out.putAll(fieldTypes(named.type(), symbols));
                }
            }
            for (Hir.Field f : d.fields()) {
                // an example builds its input through a decoder, so a field with no external
                // representation is not one it can state; the data declaration refused it already
                if (f.type() instanceof Hir.TypeRef ref) {
                    out.put(f.name(), ref);
                }
            }
        }
        return out;
    }

    /**
     * The type a written type denotes. The {@code TypeRef} comes from the module that declares the
     * data, and it says what it denotes — resolved where it was written, so naming a type this
     * module never imported is not a question asked here at all.
     */
    public static Type shapeOf(Hir.TypeRef declaredType) {
        return declaredType == null ? null : declaredType.denotes();
    }
}
