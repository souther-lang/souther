package souther.compiler.program;

/**
 * What a call to a behavior reaches: what it takes and answers, and where its implementation comes
 * from.
 *
 * <p>What a caller has to know. A call carries the identity resolution gave it, and an output
 * emitting one has to know what to hand over, what comes back, and whether what it emits is a call
 * into what it is emitting, a call into something built elsewhere, or a crossing to an
 * implementation supplied from outside Souther.
 *
 * <p>Answered for a behavior of a module this compile read off the path as much as for one of its
 * own. That module is not among {@link CheckedProgram#modules()} — this compile did not check it —
 * but its declarations were read here, because a body naming one had to be checked against them.
 *
 * <p>One value and not a reading of one. This is what a behavior of a checked module holds too
 * ({@link CheckedBehavior#signature}, {@link CheckedBehavior#implementation}), so a behavior
 * written here says what it takes and where its implementation comes from once, whether it is
 * reached through the module being emitted or through the identity a call carries. What follows is
 * that a target for a behavior written here carries the implementation itself — a
 * {@link CheckedImplementation.Body} holds the Core the checker typed — which a caller has no use
 * for and does not look at. Cut to what a caller reads, it would be a second value made from this
 * one, and the two would say the same thing until either was made from something else.
 *
 * <p>Where the two readings of what a behavior takes are held to each other. A signature says the
 * inputs as types and a body says the bindings they arrive in, and lists of different lengths would
 * make reading them as one parameter wrong at some index rather than refused. Held here rather than
 * beside a behavior of a checked module, so that a target is a call boundary that cannot say two
 * things wherever one is made.
 *
 * <p>A class and not a record. What a call boundary is known to be will grow — what a caller may
 * assume of the answer is a decision this compilation does not make for a behavior another module
 * declared ({@link souther.compiler.core.EnsuresEnforcement.NotDecidedHere}) — and each of those
 * arrives as a question a reader asks rather than as a place in a constructor every existing reader
 * would have to be recompiled against.
 */
public final class BehaviorTarget {

    private final CheckedSignature signature;
    private final CheckedImplementation implementation;

    BehaviorTarget(CheckedSignature signature, CheckedImplementation implementation) {
        if (signature == null || implementation == null) {
            throw new IllegalArgumentException(
                    "a call boundary is what it takes and answers and where its implementation"
                            + " comes from");
        }
        if (implementation instanceof CheckedImplementation.Body body
                && body.parameters().size() != signature.takes().size()) {
            // Said with both readings written out. The identity a caller asks with is not here —
            // it is what this is filed under — so what tells the two apart is what each of them
            // says the behavior takes.
            throw new IllegalArgumentException("a behavior declared " + signature
                    + " has a body binding " + body.parameters());
        }
        this.signature = signature;
        this.implementation = implementation;
    }

    /** What it takes and what it answers, as the check settled them. */
    public CheckedSignature signature() {
        return signature;
    }

    /** Where the implementation comes from. */
    public CheckedImplementation implementation() {
        return implementation;
    }
}
