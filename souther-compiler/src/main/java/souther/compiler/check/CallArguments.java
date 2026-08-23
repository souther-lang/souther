package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.semantics.ArgumentRef;
import souther.compiler.semantics.Combinator;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;

/**
 * The argument a fact about an operation names, found in a call to it.
 *
 * <p>Between the word and the call. What {@link ArgumentRef#TheContainer} and
 * {@link ArgumentRef#TheClosure} are positions of is read off the library's own declaration
 * ({@link Combinators}), and a fact that had to reach for that to say which argument it is about
 * would be a fact written where name resolution can be seen — which is the arrangement the
 * declarations were moved out of.
 *
 * <p>So this is not a reader reinterpreting the cases. It is the one that has both halves: the word
 * a fact wrote, and the environment it takes to read that word. The same division
 * {@link AffineForms.Reading} already makes.
 *
 * <p>Nothing outside this asks for the number. A caller is answered with the argument.
 */
public final class CallArguments {

    /** The argument {@code call} passes where {@code ref} names. */
    public static Core of(ArgumentRef ref, Core.PreservedCall call) {
        return call.args().get(positionIn(ref, call.operation()));
    }

    /** {@code call} with that argument replaced by {@code value}. */
    public static Core.PreservedCall replacedIn(ArgumentRef ref, Core.PreservedCall call,
                                                Core value) {
        List<Core> args = new ArrayList<>(call.args());
        args.set(positionIn(ref, call.operation()), value);
        return new Core.PreservedCall(call.operation(), args, call.type(), call.pos());
    }

    /**
     * Which parameter of {@code operation} {@code ref} names.
     *
     * <p>A written position is itself. The two that are named by the part they play are the
     * library's to say, and an operation whose signature hands its closure nothing a container
     * holds has neither — a fact naming one of them there is a fact about an argument that is not
     * there, and it is said rather than answered with a number that would be wrong.
     */
    public static int positionIn(ArgumentRef ref, ValueName operation) {
        return switch (ref) {
            case ArgumentRef.At at -> at.position();
            case ArgumentRef.TheContainer _ -> handing(operation, "the container").containerArg();
            case ArgumentRef.TheClosure _ -> handing(operation, "the closure").closureArg();
        };
    }

    private static Combinator handing(ValueName operation, String part) {
        Combinator handed = Combinators.of(operation);
        if (handed == null) {
            throw new IllegalStateException("a rule about " + operation + " names " + part
                    + " of what it hands its closure, and its signature says it hands one nothing"
                    + " a container holds");
        }
        return handed;
    }

    private CallArguments() {}
}
