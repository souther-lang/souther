package souther.compiler.observe;

import souther.compiler.types.TypeSymbol;

import java.util.List;

/**
 * What a text stated of an answer, at the grain it stated it.
 *
 * <p>Two grains and one place they are told apart. A statement writes a value, or it names the case
 * the answer is and nothing under it — {@code | Approved} says which case and says nothing about
 * what is in it, and that is weaker evidence and still evidence. Whether an answer keeps what was
 * stated is asked here, so the two grains are one question with one answer: a reader that tested
 * for one of them would have the other grain's comparison somewhere else, and two comparisons of
 * one statement can disagree.
 *
 * <p>Asked with what it needs rather than with whoever holds it. {@link ValueTypes} says what a
 * declaration reads a place through and {@code answers} is where the answer stands, and those are
 * the whole of the context: nothing here reads a program, a module or a compiler.
 */
public sealed interface Expectation {

    /**
     * Whether {@code answered} is what this states.
     *
     * @param answered what came out, as it was observed
     * @param types    what the declarations say stands inside a value
     * @param answers  where the answer stands, which says what a sequence there is
     */
    Verdict compare(ObservedValue answered, ValueTypes types, Position answers);

    /** The whole value. */
    record TheValue(Asserted value) implements Expectation {

        public TheValue {
            if (value == null) {
                throw new IllegalArgumentException("a stated value is a value");
            }
        }

        @Override
        public Verdict compare(ObservedValue answered, ValueTypes types, Position answers) {
            Mismatch differs = new ValueMatch(types).compare(value, answered, answers);
            return differs == null ? Verdict.HELD : new Verdict.NotHeld(differs);
        }
    }

    /**
     * The case the answer is, and nothing under it.
     *
     * <p>Compared on the case, because there is no value under it to compare: holding a whole value
     * against it would report a difference that was never stated. The case an answer is is the
     * declaration it is of, which is what the reading that produced the answer already settled.
     */
    record TheCase(TypeSymbol name) implements Expectation {

        public TheCase {
            if (name == null) {
                throw new IllegalArgumentException("a stated case is a case");
            }
        }

        @Override
        public Verdict compare(ObservedValue answered, ValueTypes types, Position answers) {
            if (answered.unread() != null) {
                return new Verdict.NotHeld(new Mismatch(List.of(), Mismatch.Reason.UNREADABLE,
                        this, answered, answers));
            }
            return name.equals(answered.declaredAs()) ? Verdict.HELD
                    : new Verdict.NotHeld(new Mismatch(List.of(), Mismatch.Reason.TYPE, this,
                            answered, answers));
        }
    }
}
