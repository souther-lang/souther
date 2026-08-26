package souther.compiler.check;

import souther.compiler.DefaultStdlib;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.core.Core;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

/**
 * Which library operations answer what their container holds accumulated: started from an identity
 * and carried through one binary combine over the accumulator and an element, both of the type the
 * operation answers.
 *
 * <p>The sibling of {@link Reductions}, and separate for the reason that is separate from
 * {@link Combinators}. A reduction is handed the step it repeats and this is not: {@code List.sum}
 * takes a container and nothing else, so what it starts from and what it repeats are not arguments
 * anything can read off the call — they are what the operation means, and are written down here.
 * {@link Question#ACCUMULATION} states the range and this answers it.
 *
 * <p>What is written down is a recipe and not a value. {@code List.concat} starts from the empty
 * list of a type its declaration does not name — {@code (List<List<'a>>) -> List<'a>} leaves
 * {@code 'a} to the call — and {@code List.sum} starts from a nought that is an {@code Int} at one
 * call and a {@code Decimal} at the next (ADR-0082). So the identity is named as the value it is and
 * instantiated at the type the call answers, where a reader needs one; a table holding a
 * {@link souther.compiler.core.Core} literal would have to have decided that already.
 *
 * <p>Nothing here knows what any check can do with an answer. The domain that reads bounds carries
 * numbers and no strings, and that is a fact about the reader, not about {@code String.concat},
 * which accumulates exactly as {@code List.concat} does. A registry that left it out because nothing
 * downstream could use it would be answering a different question than the one it is named for —
 * and would say, to the next reader, that the library's own definition of {@code concat} as
 * {@code join("", xs)} is not what it says. What may be read as a number is asked after this, by
 * whoever needs it to be one.
 */
final class Accumulations {

    /** What an accumulation starts from, as the value it is rather than as a term of some type. */
    enum Identity {
        ZERO,
        ONE,
        EMPTY
    }

    /** The step it repeats over the accumulator and an element. */
    enum Combine {
        ADD,
        MULTIPLY,
        APPEND
    }

    /** An accumulation: what it starts from, and the step it repeats. */
    record Accumulation(Identity identity, Combine combine) {}

    /** What a call accumulates, and the container it accumulates over. */
    record Accumulating(Accumulation what, Core container) {}

    /**
     * The operations that accumulate, and what each is.
     *
     * <p>{@code List.concat} and {@code String.concat} are here beside the two numeric ones because
     * they are the same shape said of other values: a list of lists joined from the empty list, a
     * list of strings joined from the empty string. The library states the second as
     * {@code join("", xs)} itself.
     */
    private static final Map<ValueName.Stdlib.Operation, Accumulation> ACCUMULATES = accumulates();

    private static Map<ValueName.Stdlib.Operation, Accumulation> accumulates() {
        Map<ValueName.Stdlib.Operation, Accumulation> stated = new LinkedHashMap<>();
        stated.put(op("List", "sum"), new Accumulation(Identity.ZERO, Combine.ADD));
        stated.put(op("List", "product"), new Accumulation(Identity.ONE, Combine.MULTIPLY));
        stated.put(op("List", "concat"), new Accumulation(Identity.EMPTY, Combine.APPEND));
        stated.put(op("String", "concat"), new Accumulation(Identity.EMPTY, Combine.APPEND));
        return stated;
    }

    /**
     * The operations in range that accumulate from no identity through no single step.
     *
     * <p>{@code String.join} is one, and not because it answers a string. A separator stands between
     * elements and not before the first, so what the walk does at each element depends on whether
     * anything came before it — and an identity with a combine over two values of one type has
     * nowhere to keep that. Written as {@code join(sep, xs)} it is a walk carrying more than the
     * answer so far, which is a different question from this one and is not asked of it here.
     */
    static final Set<ValueName> NO_SIMPLE_ACCUMULATION = Set.of(op("String", "join"));

    /** What {@code operation} accumulates, or null where it accumulates nothing — including where
     * the name is not a library operation. */
    static Accumulation of(ValueName operation) {
        // A name that is no library operation accumulates nothing, and is answered by the type
        // rather than by a lookup that finds nothing.
        return operation instanceof ValueName.Stdlib.Operation library
                ? Derived.RULES.get(library) : null;
    }

    /**
     * What {@code call} accumulates and over what, or null where it accumulates nothing.
     *
     * <p>Which argument holds the elements is not written down. An accumulation answers a value of
     * the type its container holds, so the argument that holds them is the one whose elements are of
     * the type the operation answers — which the declaration already says, in the same way it says
     * where a {@link Reductions reduction}'s seed is. A signature admitting two readings of it is
     * refused where the rules are read rather than answered by half.
     */
    static Accumulating accumulating(Core.PreservedCall call) {
        if (!(call.operation() instanceof ValueName.Stdlib.Operation operation)) {
            return null;
        }
        Accumulation what = of(operation);
        Integer container = Derived.CONTAINERS.get(operation);
        return what == null || container == null || container >= call.args().size() ? null
                : new Accumulating(what, call.args().get(container));
    }

    /** The operations there is a rule about, for the check that a rule answers a question its
     * operation is asked. */
    static Set<ValueName.Stdlib.Operation> answered() {
        return Derived.RULES.keySet();
    }

    /** Read once, and held to the library while it is read. The library is the same library for
     * every module compiled. */
    private static final class Derived {
        private static final Map<ValueName.Stdlib.Operation, Accumulation> RULES =
                read(DefaultStdlib.get());
        private static final Map<ValueName.Stdlib.Operation, Integer> CONTAINERS =
                containers(DefaultStdlib.get());
    }

    /**
     * The rules, checked against the declarations they are about.
     *
     * <p>A rule under a name the library does not declare is a rule nothing reaches, and is the
     * defect {@link Question} exists to catch seen from the other end — so it is raised here, where
     * the name is read, rather than left to a test.
     */
    /* A pure function of the library, so the holder above is the only thing here that reaches for
     * the process's own — {@link souther.compiler.DefaultStdlib} says who may and why the loader
     * may not. */
    private static Map<ValueName.Stdlib.Operation, Accumulation> read(Stdlib stdlib) {
        Map<ValueName.Stdlib.Operation, Accumulation> rules = new LinkedHashMap<>();
        ACCUMULATES.forEach((operation, accumulation) -> {
            if (stdlib.entry(operation) == null) {
                throw new IllegalStateException(operation + " is named an accumulation and the"
                        + " library declares no such operation");
            }
            rules.put(operation, accumulation);
        });
        return Collections.unmodifiableMap(rules);
    }

    /**
     * Which argument each accumulation holds its elements in, read off the declarations.
     *
     * <p>The half a signature answers, kept apart from the half it does not, as {@link Reductions}
     * keeps them apart. An operation answering a value of the type one of its containers holds is
     * the range {@link Question#ACCUMULATION} is drawn on, so a rule here has such an argument by
     * construction; two of them would be a declaration that does not say which it walks, and is
     * refused rather than guessed at.
     */
    private static Map<ValueName.Stdlib.Operation, Integer> containers(Stdlib stdlib) {
        Map<ValueName.Stdlib.Operation, Integer> where = new LinkedHashMap<>();
        Derived.RULES.keySet().forEach(operation -> {
            Stdlib.Signature signature = stdlib.entry(operation).signature();
            int found = -1;
            for (int i = 0; i < signature.params().size(); i++) {
                Type element = Type.elementOfAContainer(signature.params().get(i));
                if (element == null || !element.equals(signature.result())) {
                    continue;
                }
                if (found >= 0) {
                    throw new IllegalStateException(operation + " is named an accumulation and takes"
                            + " two containers of what it answers, so which one it walks is not read"
                            + " off its signature");
                }
                found = i;
            }
            if (found < 0) {
                throw new IllegalStateException(operation + " is named an accumulation and takes no"
                        + " container of the type it answers");
            }
            where.put(operation, found);
        });
        return Collections.unmodifiableMap(where);
    }

    /** The operation {@code name} of the library module published as {@code alias}, written as the
     * two values a library name is made of — the spelling {@link Reductions} states its own rows
     * in. */
    private static ValueName.Stdlib.Operation op(String alias, String name) {
        return ValueName.Stdlib.operation(alias, name);
    }

    private Accumulations() {}
}
