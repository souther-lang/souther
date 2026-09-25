package souther.compiler.program;

import souther.compiler.types.ValueName;

import java.util.List;

/**
 * What an output reaching a behavior has to know about calling it and constructing it: what it
 * takes and answers, where its implementation comes from, and what constructing it requires
 * injected.
 *
 * <p>A call carries the identity resolution gave it, and an output emitting one has to know what to
 * hand over, what comes back, and whether what it emits is a call into what it is emitting, a call
 * into something built elsewhere, or a crossing to an implementation supplied from outside Souther.
 * An output building a composition has to know, of each stage, what that stage's construction is
 * handed — whichever module declares the stage.
 *
 * <p>Answered for a behavior of a module this compile read off the path as much as for one of its
 * own. That module is not among {@link CheckedProgram#modules()} — this compile did not check it —
 * but its declarations were read here, because a body naming one had to be checked against them.
 *
 * <p>One value and not a reading of one. This is what a behavior of a checked module holds too
 * ({@link CheckedBehavior#signature}, {@link CheckedBehavior#implementation},
 * {@link CheckedBehavior#requirements}), so a behavior written here says what it takes, where its
 * implementation comes from and what constructing it requires once, whether it is reached through
 * the module being emitted or through the identity a call carries. What follows is that a target
 * for a behavior written here carries the implementation itself — a
 * {@link CheckedImplementation.Body} holds the Core the checker typed — which a caller has no use
 * for and does not look at. Cut to what a caller reads, it would be a second value made from this
 * one, and the two would say the same thing until either was made from something else.
 *
 * <p>Where the two readings of what a behavior takes are held to each other. A signature says the
 * inputs as types and a body says the bindings they arrive in, and lists of different lengths would
 * make reading them as one parameter wrong at some index rather than refused. Held here rather than
 * beside a behavior of a checked module, so that a target cannot say two things wherever one is
 * made.
 *
 * <p>Where the form of the signature is held to the implementation. A declaration names every
 * parameter and a composition names none, and only a composition is {@link
 * CheckedImplementation.Composed}; a body, an injected behavior and an unwritten one are each a
 * declaration. An implementation another compile emitted is either, and the signature says which
 * ({@link CheckedSignature#declaredParameters()}).
 *
 * <p>Where the construction requirements are held to the implementation. Souther does not construct
 * an injected behavior — Java supplies it whole — so an injected one requires nothing to construct,
 * and a target saying otherwise is refused. That is the only implementation held to it: an
 * unwritten behavior may declare what it depends on before anyone writes it, and what it requires
 * is not where its implementation comes from.
 *
 * <p>A class and not a record. What a target is known to be will grow — what a caller may
 * assume of the answer is a decision this compilation does not make for a behavior another module
 * declared ({@link souther.compiler.core.EnsuresEnforcement.NotDecidedHere}) — and each of those
 * arrives as a question a reader asks rather than as a place in a constructor every existing reader
 * would have to be recompiled against.
 */
public final class BehaviorTarget {

    private final CheckedSignature signature;
    private final CheckedImplementation implementation;
    private final List<ValueName.Behavior> requirements;

    BehaviorTarget(CheckedSignature signature, CheckedImplementation implementation,
                   List<ValueName.Behavior> requirements) {
        if (signature == null || implementation == null || requirements == null) {
            throw new IllegalArgumentException(
                    "a behavior target is what it takes and answers, where its implementation"
                            + " comes from and what constructing it requires");
        }
        holdTheFormOfTheSignature(signature, implementation);
        if (implementation instanceof CheckedImplementation.Injected && !requirements.isEmpty()) {
            throw new IllegalArgumentException("an injected behavior is not constructed by"
                    + " Souther, and is said to require " + requirements);
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
        this.requirements = List.copyOf(requirements);
    }

    // No wildcard arm: an implementation added later does not compile until it is decided here
    // which form of signature it goes with.
    private static void holdTheFormOfTheSignature(CheckedSignature signature,
                                                  CheckedImplementation implementation) {
        boolean declared = signature.declaredParameters().isPresent();
        switch (implementation) {
            case CheckedImplementation.Body _,
                 CheckedImplementation.Injected _,
                 CheckedImplementation.Unwritten _ -> {
                if (!declared) {
                    throw new IllegalArgumentException("a composition's signature " + signature
                            + " names no parameters, and " + implementation
                            + " is written against a declaration");
                }
            }
            case CheckedImplementation.Composed _ -> {
                if (declared) {
                    throw new IllegalArgumentException("a declared signature " + signature
                            + " is not the signature of " + implementation);
                }
            }
            case CheckedImplementation.ImplementedElsewhere _ -> { }
        }
    }

    /** What it takes and what it answers, as the check settled them. */
    public CheckedSignature signature() {
        return signature;
    }

    /** Where the implementation comes from. */
    public CheckedImplementation implementation() {
        return implementation;
    }

    /**
     * The behaviors constructing this one requires injected, in the order its constructor takes
     * them: first appearance, stages left to right.
     *
     * <p>Construction requirements, and read together with {@link #implementation()}. Empty for an
     * injected behavior, because Souther does not construct one — which is not the same as a
     * behavior that can be called by name with nothing handed: an injected behavior is itself the
     * dependency of whatever names it. For a behavior another compile emitted this is what that
     * compile published, so a composition here hands such a stage the same list its constructor
     * was built to take.
     *
     * <p>The dependency identities alone, and not which definition asked for each: that is a
     * compiler diagnostic's concern, and every output that emits a constructor parameter, a
     * capture, a stage's context or an example's fake wants only this list and its order.
     */
    public List<ValueName.Behavior> requirements() {
        return requirements;
    }
}
