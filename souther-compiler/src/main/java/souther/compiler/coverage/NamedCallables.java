package souther.compiler.coverage;

import souther.compiler.ast.Hir;
import souther.compiler.types.BindingId;
import souther.compiler.types.ValueName;

import java.util.LinkedHashMap;
import java.util.Map;

/**
 * Which callable each name a body binds one to stands for.
 *
 * <p>A name bound to a callable is where the callable was put; what it stands for is the
 * declaration. Read as the name it was bound under, a call through it is a call to a declaration of
 * that name -- and there is none, so nothing answers about it. That reaches two questions at once:
 * what the call answers out of, which then falls back to reading every argument, and which
 * declaration the copy it makes is of.
 *
 * <p>Carried down the body rather than gathered over it, because a name means what the nearest
 * binding of it gave it. Chains keep the answer: {@code let g = f} stands for whatever {@code f}
 * does.
 *
 * <p>One reading, asked where the declarations are walked and asked again where a body is expanded.
 * The two ask it of the same tree and act on it differently — one decides what a fork rests on, the
 * other which declaration a copy is of — and written apart they would agree by having been derived
 * alike, until the day one of them learned a shape the other did not.
 */
public record NamedCallables(Map<BindingId, String> byBinding) {

    /** Nothing bound. */
    public static final NamedCallables NONE = new NamedCallables(Map.of());

    public NamedCallables {
        byBinding = Map.copyOf(byBinding);
    }

    /**
     * Which declaration {@code named} reaches, following what a name was bound to.
     *
     * <p>{@code null} where it names no declaration at all -- a parameter holding a function, say,
     * whose callable is decided by whoever called this.
     */
    public String reached(Hir.Var.Denoting named) {
        return named.denotes() instanceof ValueName.Local local ? byBinding.get(local.id())
                : named.reaches();
    }

    /** The same, with {@code binding} standing for whatever {@code value} is. */
    public NamedCallables and(BindingId binding, Hir.Expr value) {
        String callable = value instanceof Hir.Var.Denoting named ? reached(named) : null;
        if (binding == null || callable == null) {
            return this;
        }
        Map<BindingId, String> wider = new LinkedHashMap<>(byBinding);
        wider.put(binding, callable);
        return new NamedCallables(wider);
    }
}
