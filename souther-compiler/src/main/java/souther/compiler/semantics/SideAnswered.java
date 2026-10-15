package souther.compiler.semantics;

import java.util.Objects;

/**
 * One way a value can come out, as a statement: which side of it, and which answer on that side.
 *
 * <p>A side alone is a question and not a statement. {@code List.any} and {@code List.all} both
 * answer a truth and both hand their closure a truth to answer, and they mean opposite things: one
 * holds where some element's answer is true, the other fails where some element's answer is false.
 * What tells them apart is which answer, so the answer is part of what is said.
 *
 * @param aspect which side of the value
 * @param holds  the answer on that side the statement is about: true is "holds", "holds something",
 *               "holds a value"
 */
public record SideAnswered(AnswerAspect aspect, boolean holds) {

    public SideAnswered {
        Objects.requireNonNull(aspect, "an answer is on some side of a value");
    }
}
