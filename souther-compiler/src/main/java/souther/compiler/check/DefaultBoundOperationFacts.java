package souther.compiler.check;

import souther.compiler.DefaultStdlib;

/**
 * The facts about the language's operations, held to the library this compiler ships, read once
 * for the process.
 *
 * <p>A lifecycle and nothing else, as {@link DefaultStdlib} is for the library. What is held is a
 * pure function of the declarations and the shipped library ({@link OperationFactBinder#bindAll}),
 * so it is a constant of this compiler — the same for every compilation and under any backend —
 * and threading it from a construction site would put a value in a dozen signatures to say
 * something none of them varies in. A reader that binds against a library of its own asks the
 * binder with that library and holds the answer itself.
 *
 * <p>What it publishes is a complete {@link BoundOperationFacts} or nothing at all: the holder's
 * class initializer runs the binding to completion before {@link #get} can return, so no reader
 * can catch the facts half held. That, and not an initialization order somewhere else, is what
 * says the binding has run for every fact a reader reaches through here — there is no other way to
 * one.
 */
public final class DefaultBoundOperationFacts {

    private DefaultBoundOperationFacts() {
    }

    /** Bound when first asked for, not when this class is mentioned. */
    private static final class Holder {
        private static final BoundOperationFacts INSTANCE =
                OperationFactBinder.bindAll(DefaultStdlib.get());
    }

    /** The facts, held to the shipped library. */
    public static BoundOperationFacts get() {
        return Holder.INSTANCE;
    }
}
