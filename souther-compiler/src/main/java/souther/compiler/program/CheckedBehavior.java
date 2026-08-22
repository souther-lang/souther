package souther.compiler.program;

import souther.compiler.types.ValueName;

/**
 * One behavior of a checked module: what it is called, what it takes and answers, and where its
 * implementation comes from.
 *
 * <p>A class and not a record. What a checked behavior is known to be will grow — what it requires,
 * what it declares cannot arrive, what its examples said — and each of those is something a reader
 * asks for rather than a place in a constructor every existing reader would have to be recompiled
 * against.
 */
public final class CheckedBehavior {

    private final ValueName.Behavior name;
    private final CheckedSignature signature;
    private final CheckedImplementation implementation;

    CheckedBehavior(ValueName.Behavior name, CheckedSignature signature,
                    CheckedImplementation implementation) {
        this.name = name;
        this.signature = signature;
        this.implementation = implementation;
    }

    /**
     * The name this behavior is reached by.
     *
     * <p>The resolved name and not a spelling. Two modules may declare a behavior of one name, and
     * what a body's call reaches is this — so a reader holding one of these can be asked for by a
     * call site without putting a module and a name back together.
     */
    public ValueName.Behavior name() {
        return name;
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
        return name.module() + "." + name.name();
    }
}
