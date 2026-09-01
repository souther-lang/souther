package souther.compiler.program;

/**
 * What a call to a behavior reaches: what it takes and answers, and where its implementation comes
 * from.
 *
 * <p>What a caller needs and no more. A call carries the identity resolution gave it, and an output
 * emitting one has to know what to hand over, what comes back, and whether what it emits is a call
 * into what it is emitting, a call into something built elsewhere, or a crossing to an
 * implementation supplied from outside Souther. None of that is the callee's body: an output
 * emitting a behavior's implementation reaches it by walking {@link CheckedProgram#modules()},
 * which is a different question with a different answer.
 *
 * <p>So this is answered for a behavior of a module this compile read off the path as much as for
 * one of its own. That module is not among {@link CheckedProgram#modules()} — this compile did not
 * check it — but its declarations were read here, because a body naming one had to be checked
 * against them.
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

    @Override
    public String toString() {
        return signature + " " + implementation;
    }
}
