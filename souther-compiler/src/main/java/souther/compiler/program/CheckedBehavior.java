package souther.compiler.program;

import souther.compiler.core.EnsuresEnforcement;
import souther.compiler.types.ValueName;

import java.util.List;

/**
 * One behavior of a checked module: what it is called, what it takes and answers, and where its
 * implementation comes from.
 *
 * <p>A class and not a record. What a checked behavior is known to be will grow — what it requires,
 * what it declares cannot arrive — and each of those is something a reader asks for rather than a
 * place in a constructor every existing reader would have to be recompiled against.
 */
public final class CheckedBehavior {

    private final ValueName.Behavior name;
    private final CheckedSignature signature;
    private final CheckedImplementation implementation;
    private final EnsuresEnforcement ensures;
    private final List<CheckedRow> rows;

    CheckedBehavior(ValueName.Behavior name, CheckedSignature signature,
                    CheckedImplementation implementation, EnsuresEnforcement ensures,
                    List<CheckedRow> rows) {
        // The one place the two readings of what a behavior takes meet, and so the one place they
        // are held to each other. A signature says the inputs as types and a body says the bindings
        // they arrive in; a reader is offered them as one parameter at each index, and lists of
        // different lengths would make that reading wrong at some index rather than refused.
        if (implementation instanceof CheckedImplementation.Body body
                && body.parameters().size() != signature.takes().size()) {
            throw new IllegalArgumentException("`" + name.module() + "." + name.name() + "` takes "
                    + signature.takes().size() + " and its body binds " + body.parameters().size());
        }
        this.name = name;
        this.signature = signature;
        this.implementation = implementation;
        this.ensures = ensures;
        this.rows = List.copyOf(rows);
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

    /**
     * What this behavior declares about its answer, and where that is held to.
     *
     * <p>The two together, because an output needs both and neither is worth having alone: a
     * contract with nowhere to check it is a rule nothing runs, and a placement with no rule is a
     * check with nothing in it. {@link EnsuresEnforcement.AtTheCallee} is checked where the
     * behavior answers, so a caller emits nothing;
     * {@link EnsuresEnforcement.AtEachCrossing} is a behavior whose answer arrives from outside, so
     * every crossing into what this program emits checks it;
     * {@link EnsuresEnforcement.NoContract} is a behavior that declares nothing.
     *
     * <p>{@link EnsuresEnforcement.NotDecidedHere} is for a behavior another module declared, and
     * no behavior of this program is one — every module here was compiled together. It is an arm of
     * the answer all the same, because collapsing it would make "there is no check" and "nobody
     * decided" one sentence.
     */
    public EnsuresEnforcement ensures() {
        return ensures;
    }

    /**
     * What its {@code example} rows say it answers, in the order they are written.
     *
     * <p>Every row recorded for it, whichever source wrote it: a behavior may be exampled in its
     * own module and in any number of attached {@code examples for} files, and which file a row is
     * in is a fact about the row ({@link CheckedRow#at}) rather than something a reader picks
     * between before it can ask what the behavior owes.
     *
     * <p>Every row and not the ones that could be handed over as values. A row this compile could
     * not read whole is here saying so, because a reader given nothing for it would count a row it
     * never saw among the ones it walked and found nothing wrong with — and a behavior would read
     * as having said nothing about an input someone wrote down.
     *
     * <p>Empty where the behavior is exampled nowhere, which is a behavior nothing says what it
     * owes.
     */
    public List<CheckedRow> rows() {
        return rows;
    }

    @Override
    public String toString() {
        return name.module() + "." + name.name();
    }
}
