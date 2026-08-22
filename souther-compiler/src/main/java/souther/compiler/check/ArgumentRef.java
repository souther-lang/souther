package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;

/**
 * Which argument of a call a rule about an operation names.
 *
 * <p>A locator and nothing more. Either the position the declaration writes, or the part the
 * argument plays in what the operation hands its closure — which {@link Combinators} already reads
 * off the signature. A rule naming the part restates nothing and cannot come to disagree with the
 * declaration; one writing a position is a decision the signature does not settle, and is held to
 * the declaration where the tables are bound.
 *
 * <p>Beside {@link Combinators} and not under any one reader. What an operation does to the values it
 * is given is asked by more than one check — what a construction keeps of its source, where an
 * element of an answer came from, whether a recursion is structural — and each of them has to say
 * which argument it is talking about. Held inside the reader that happened to need it first, every
 * other reader would depend on that one to say the word "argument", which is a dependency between
 * two consumers with nothing between them.
 *
 * <p>Nothing outside this asks for the number. A reader is answered with the argument.
 */
public sealed interface ArgumentRef {

    /** Which parameter of {@code operation} this names. */
    int positionIn(ValueName operation);

    /** The argument {@code call} passes there. */
    default Core of(Core.PreservedCall call) {
        return call.args().get(positionIn(call.operation()));
    }

    /** {@code call} with that argument replaced by {@code value}. */
    default Core.PreservedCall replacedIn(Core.PreservedCall call, Core value) {
        List<Core> args = new ArrayList<>(call.args());
        args.set(positionIn(call.operation()), value);
        return new Core.PreservedCall(call.operation(), args, call.type(), call.pos());
    }

    /** The argument at a written position. */
    record At(int position) implements ArgumentRef {
        @Override
        public int positionIn(ValueName operation) {
            return position;
        }
    }

    /** The argument holding what the operation hands its closure. */
    record TheContainer() implements ArgumentRef {
        @Override
        public int positionIn(ValueName operation) {
            return handing(operation, "the container").containerArg();
        }
    }

    /** The argument the operation applies to what a container holds. */
    record TheClosure() implements ArgumentRef {
        @Override
        public int positionIn(ValueName operation) {
            return handing(operation, "the closure").closureArg();
        }
    }

    private static Combinators.Combinator handing(ValueName operation, String part) {
        Combinators.Combinator handed = Combinators.of(operation);
        if (handed == null) {
            throw new IllegalStateException("a rule about " + operation + " names " + part
                    + " of what it hands its closure, and its signature says it hands one nothing"
                    + " a container holds");
        }
        return handed;
    }
}
