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
 * What a declaration already says about a value a fixture wrote.
 *
 * <p>One walk, read by both of the things that need it: the reading that builds a row, and the pass
 * that decides which methods a row's calls need emitted. Two walks would be two answers about which
 * calls are applicable, and the one that answered later would find no method.
 *
 * <p>Nothing is run. Every step reads a name {@code Resolve} already settled or a declaration a
 * module already made, so asking costs no helper a second application against a row's budget.
 *
 * @param values the definitions a name in a fixture may stand for
 * @param bound  what a {@code let} has in force where the walk starts, which the walk adds to as it
 *               enters more of them
 */
public record FixtureEvidence(Symbols symbols, Map<String, Hir.FnDef> values,
                              Map<BindingId, Hir.Expr> bound) {

    public FixtureEvidence(Symbols symbols, Map<String, Hir.FnDef> values) {
        this(symbols, values, Map.of());
    }

    /** The same, with {@code binding} standing for {@code value} as well. */
    public FixtureEvidence with(BindingId binding, Hir.Expr value) {
        Map<BindingId, Hir.Expr> wider = new LinkedHashMap<>(bound);
        wider.put(binding, value);
        return new FixtureEvidence(symbols, values, wider);
    }

    /**
     * What {@code e} is declared to be, or null where no declaration says — which is where a helper
     * stands, since what a helper was declared to answer with is not read and what it supplied is
     * its answer's to say.
     */
    public Type declaredTypeOf(Hir.Expr e) {
        return declaredTypeOf(e, new HashSet<>(), new HashMap<>(bound));
    }

    /** As above, from a walk that already has names in force and a record of what it has entered. */
    public Type declaredTypeOf(Hir.Expr e, Set<ValueName> seen, Map<BindingId, Hir.Expr> inForce) {
        return switch (e) {
            case Hir.NewData nd -> Type.ref(nd.typeName().denotes());
            // `AmountN(100)` is the newtype's construction written in call form (ADR-0032).
            case Hir.Apply c when constructsANewtype(c) -> Type.ref(constructs(c));
            case Hir.FieldAccess fa -> {
                Type target = declaredTypeOf(fa.target(), seen, inForce);
                yield target == null ? null : fieldTypeOf(target, fa.field());
            }
            case Hir.LetIn let -> {
                BindingId binding = let.binder().id();
                Hir.Expr outer = inForce.put(binding, let.value());
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
            case Hir.Var v -> {
                ValueName denotes = v.denotes();
                // A name reached twice is the cycle the reading itself reports; this walk only stops.
                if (denotes == null || !seen.add(denotes)) {
                    yield null;
                }
                Hir.Expr body = denotes instanceof ValueName.Local local
                        ? inForce.get(local.id())
                        : valueBody(v.name());
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
        if (!(record instanceof Type.Ref r)) {
            return null;
        }
        TypeSymbol named = r.name();
        if (isNewtype(named)) {
            // A newtype declares one field, and it is what it wraps (ADR-0032).
            return "value".equals(field) ? shapeOf(newtypeBaseType(named, symbols)) : null;
        }
        return shapeOf(fieldTypes(named, symbols).get(field));
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
        return c.denotes() instanceof ValueName.OfType named ? named.type() : null;
    }

    // --- what a declaration says, asked of the resolution and never of a spelling ------------------

    /**
     * Whether {@code name} is a newtype. Asked of a name resolution settled, never of a spelling: an
     * imported value's body names its own module's types, which the module reading the row need not
     * have imported, and a module of its own may declare something else of that spelling.
     */
    public static boolean isNewtype(TypeSymbol name, Symbols symbols) {
        return name != null
                && symbols.declarations().declaration(name.key()) instanceof Hir.Data d && d.newtype();
    }

    /** The written form of what a newtype wraps, kept whole so a generic base
     *  ({@code data 在庫 = Map<商品ID, Int>}) keeps its type arguments. */
    public static Hir.TypeRef newtypeBaseType(TypeSymbol name, Symbols symbols) {
        return name != null
                && symbols.declarations().declaration(name.key()) instanceof Hir.Data d && d.newtype()
                && d.fields().size() == 1 && d.fields().get(0).type() instanceof Hir.TypeRef base
                ? base : null;
    }

    /** A data's fields by name, following the {@code ...includes} it composes in (spec §data). */
    public static Map<String, Hir.TypeRef> fieldTypes(TypeSymbol typeName, Symbols symbols) {
        Map<String, Hir.TypeRef> out = new LinkedHashMap<>();
        if (symbols.declarations().declaration(typeName.key()) instanceof Hir.Data d) {
            for (Hir.Name inc : d.includes()) {
                out.putAll(fieldTypes(inc.denotes(), symbols));
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
