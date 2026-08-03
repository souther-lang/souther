package souther.compiler.check;

import souther.compiler.types.BindingId;
import souther.compiler.types.Type;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * The variables one helper parameter carries, minted where a declaration is read.
 *
 * <p>A library signature is resolved once, when the library is loaded, and every call site reads
 * that one value; nothing instantiates it. A call builds its own bindings and substitutes, so a
 * variable the call solves becomes what it was solved to and one it does not solve comes back out as
 * the variable the library wrote. Two unrelated calls therefore hand back one name —
 * {@code List.length} and {@code Set.size} both wrote {@code 'a} — and a parameter that took its
 * answer from each of them would claim the two hold the same thing.
 *
 * <p>So the instantiation that never happened is done here, at the one place where the two can be
 * told apart: reading a declaration, with that call's bindings in hand. A variable the declaration
 * wrote and the call did not solve is the declaration's own, and is minted afresh. A variable that
 * arrived through what the position asked for was minted already — by an earlier parameter of this
 * helper, or at an outer call — and is carried through untouched. The question is where the variable
 * came from, not what it is spelled.
 *
 * <p>One declaration is instantiated once, over everything it declares at that call: a signature
 * that writes {@code 'a} in two of its parameters wrote one variable, and {@code Set.union(a, b)}
 * says the two sets hold the same thing.
 *
 * <p>A minted name is stable for a given source: it names the binding the parameter is
 * and counts the declarations read for it in the order they are read, both of which the same source
 * gives the same way twice. It carries a {@code .}, which no written type variable can — the lexer
 * takes only identifier characters after the apostrophe — so it is never a name an author or the
 * core could have written.
 */
final class Freshening {

    private String parameter = "";
    private int declarations;

    /** Starts again for {@code target}: another parameter's variables are not this one's. */
    void forParameter(BindingId target) {
        declarations = 0;
        parameter = target.toString();
    }

    /** {@code declared} with the variables it wrote replaced by this parameter's own. */
    Type instantiate(Type declared) {
        Map<String, Type> rename = renaming(List.of(declared), Map.of());
        return rename.isEmpty() ? declared : TypeOps.substitute(declared, rename);
    }

    /**
     * What to rename the variables {@code declared} wrote and {@code solved} did not solve to.
     *
     * <p>Asked of the declaration as it was written, before {@code solved} is substituted into it: a
     * variable that came in as one of {@code solved}'s answers was minted somewhere already, and
     * asking after the substitution would see it standing in the declaration and mint it again. The
     * caller substitutes both at once.
     */
    Map<String, Type> renaming(List<Type> declared, Map<String, Type> solved) {
        Map<String, Type> rename = new LinkedHashMap<>();
        for (Type t : declared) {
            collect(t, solved, rename);
        }
        if (!rename.isEmpty()) {
            declarations++;
        }
        return rename;
    }

    private void collect(Type t, Map<String, Type> solved, Map<String, Type> rename) {
        if (t == null) {
            return;
        }
        Type.mentions(t, x -> {
            if (x instanceof Type.Var v && !solved.containsKey(v.name())
                    && !rename.containsKey(v.name())) {
                rename.put(v.name(), Type.var(v.name() + "." + parameter + "." + declarations));
            }
            return false;   // a collector, not a test: every position is visited
        });
    }
}
