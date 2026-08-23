package souther.compiler.semantics;

import souther.compiler.types.ValueName;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * What is true of the language's own operations.
 *
 * <p>The declarations are the list, and everything else here is read off it. An index is derived
 * rather than declared beside the list, so a fact cannot exist without being among the
 * declarations — which is what the procedures that validate these enumerate, and what a fact added
 * later is therefore part of without anyone remembering to add it anywhere.
 *
 * <p><b>Looking one up is a lookup and nothing else.</b> Holding these to the library's own
 * declarations reads signatures, which is the frontend's; it happens once over the whole list
 * ({@code check.OperationFactBinder}) rather than on the first ask for each fact. Bound the second
 * way, a fact nothing asked for was a fact nothing checked, and the completeness of the checking
 * depended on which consumers there happened to be.
 */
public final class OperationFacts {

    /** One fact, and the operation it is about. */
    public record Declared(ValueName operation, OperationFact fact) {

        public Declared {
            java.util.Objects.requireNonNull(operation, "a fact is about an operation");
            java.util.Objects.requireNonNull(fact, "and says something");
        }
    }

    private static Declared about(String alias, String name, OperationFact fact) {
        return new Declared(new ValueName.Stdlib(alias, name), fact);
    }

    /** The argument at {@code position}, for a fact whose operation's signature does not say which
     *  one it is about. */
    private static ArgumentRef at(int position) {
        return new ArgumentRef.At(position);
    }

    /**
     * Everything declared here.
     *
     * <p>One list and not one per kind. What holds these to the library reads this, so a kind added
     * beside it would be a kind nothing validates until someone remembers — and the arrangement is
     * meant to make remembering unnecessary.
     */
    private static final List<Declared> DECLARED = List.of(
            about("Decimal", "fromInt", new OperationFact.AnswersItsArgument(at(0))));

    /** Every fact declared, for whatever holds them to the library's declarations. */
    public static List<Declared> declarations() {
        return DECLARED;
    }

    /** The argument whose number {@code operation} answers, or null where it answers none of them
     *  back. */
    public static ArgumentRef answersItsArgument(ValueName operation) {
        return Index.ANSWERS_ITS_ARGUMENT.get(operation);
    }

    /** The operations declared to answer one of their arguments. */
    public static java.util.Set<ValueName> answersItsArgument() {
        return Index.ANSWERS_ITS_ARGUMENT.keySet();
    }

    /** The indexes, read off the declarations on the first ask. */
    private static final class Index {

        private static final Map<ValueName, ArgumentRef> ANSWERS_ITS_ARGUMENT =
                index(OperationFact.AnswersItsArgument.class,
                        OperationFact.AnswersItsArgument::argument);

        private static <F extends OperationFact, V> Map<ValueName, V> index(
                Class<F> kind, java.util.function.Function<F, V> read) {
            Map<ValueName, V> out = new LinkedHashMap<>();
            for (Declared each : DECLARED) {
                if (kind.isInstance(each.fact())) {
                    V value = read.apply(kind.cast(each.fact()));
                    if (out.put(each.operation(), value) != null) {
                        throw new IllegalStateException(each.operation()
                                + " is declared to " + kind.getSimpleName() + " twice");
                    }
                }
            }
            return Map.copyOf(out);
        }
    }

    private OperationFacts() {}
}
