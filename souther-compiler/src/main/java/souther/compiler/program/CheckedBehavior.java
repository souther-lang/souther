package souther.compiler.program;

import souther.compiler.core.EnsuresEnforcement;
import souther.compiler.types.ValueName;

import java.util.List;

/**
 * One behavior of a checked module: what it is called, what it takes and answers, where its
 * implementation comes from, what it declares of its answer, and what its examples said.
 *
 * <p>The first three are its {@link BehaviorTarget}, which is what a call to it reaches and what
 * {@link CheckedProgram#behavior} answers with. Read through here as well, because a reader
 * emitting this module has the behavior in hand and would otherwise ask the program for what it is
 * already holding. It is the same value both ways: what a behavior takes and answers is one fact of
 * the program, not one per route to it.
 *
 * <p>The rest is here and nowhere else, and that is why a call is not answered with one of these. A
 * behavior a module on the path declares is reached by calls in this program and its rows were
 * never read here — handed over as a behavior with no rows it would read as one nothing says what
 * it owes, which is a different program.
 *
 * <p>A class and not a record. What a checked behavior is known to be will grow — what it requires,
 * what it declares cannot arrive — and each of those is something a reader asks for rather than a
 * place in a constructor every existing reader would have to be recompiled against.
 */
public final class CheckedBehavior {

    private final ValueName.Behavior name;
    private final BehaviorTarget target;
    private final EnsuresEnforcement ensures;
    private final List<CheckedRow> rows;

    CheckedBehavior(ValueName.Behavior name, BehaviorTarget target, EnsuresEnforcement ensures,
                    List<CheckedRow> rows) {
        this.name = name;
        this.target = target;
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
        return target.signature();
    }

    /** Where the implementation comes from. */
    public CheckedImplementation implementation() {
        return target.implementation();
    }

    /**
     * The call boundary this behavior is reached by, which is the one
     * {@link CheckedProgram#behavior} answers with.
     *
     * <p>The same value and not a copy. What a behavior takes, answers, and where its
     * implementation comes from is one fact of the program, and a call to it reaches that fact
     * whether it is reached through the module being emitted or through the identity it carries.
     */
    BehaviorTarget target() {
        return target;
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
