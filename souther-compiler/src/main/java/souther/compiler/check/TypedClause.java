package souther.compiler.check;

import souther.compiler.core.Core;

/**
 * A clause of the model as the discharge reader types it, or that typing it did not finish.
 *
 * <p>Two arms because there were two things under one null, and only one of them was ever the model
 * speaking. What was written where this used to answer {@code null} said that a clause this
 * compiler could not type is the same answer as a clause naming something outside the fragment —
 * "an answer rather than a failure". Measured over the whole suite, every one of those nulls came
 * from an exception this caught and dropped: {@code Unanswerable}, {@code IllegalStateException},
 * {@code CompileException}. The elaborator never once answered null of its own accord. So the arm
 * for a clause honestly outside what the reader types has no producer, and is not written here — an
 * arm nothing raises is an answer every clause gives by nobody having asked.
 *
 * <p>It matters downstream because the two license different sentences. From "this clause is not one
 * the reader types" follows that no guard discharges it and the run-time check is the whole of its
 * enforcement, which is about the author's model. From "typing it fell over" follows nothing at all
 * about the clause. Collapsed before a reader sees them, the second gets reported as the first, and
 * no type introduced later can take them apart again.
 */
public sealed interface TypedClause {

    /** It typed, and this is the form the reader walks. */
    record Typed(Core value) implements TypedClause {

        public Typed {
            if (value == null) {
                throw new IllegalArgumentException("a clause that typed has a form");
            }
        }
    }

    /**
     * Typing it did not finish.
     *
     * <p>Nothing about which run it was, and that is the point. This travels inside a
     * {@link StatedContract}, which is an answer a query keeps, and an answer is a value: what
     * {@code equals} says of it is what stops work downstream ({@link souther.compiler.query.Db}).
     * Carrying the exception, two runs over one unedited source answer with two objects that are
     * never equal, so every unrelated edit re-runs everything that read the contract — for as long
     * as the source is half-written, which is most of the time an editor is asking.
     *
     * <p>Which exception it was is worth having, and it goes where the rest of this check's giving
     * up goes: {@link InvariantChecker#gaveUp}, a channel about the run rather than about the model.
     * That is the same split one step out from the one this type makes — a failure and its
     * classification are not one thing either.
     */
    record Stopped() implements TypedClause {}

    /**
     * The form, or {@code null} where the typing stopped.
     *
     * <p>What the discharge check itself takes, and the one place the two are held alike on purpose:
     * the check is fail-open, so a clause it could not get a form for leaves its run-time check
     * standing, and that is the same thing to do whichever way the form went missing. Named here so
     * that it is a decision a caller takes rather than a contract every caller has to remember —
     * which is what it was, and what it was got wrong as.
     */
    default Core orNull() {
        return this instanceof Typed it ? it.value() : null;
    }
}
