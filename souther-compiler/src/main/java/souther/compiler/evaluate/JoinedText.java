package souther.compiler.evaluate;

import souther.runtime.ConstraintViolation;
import souther.runtime.Strings;

import java.util.Optional;

/**
 * The text two strings join to, where the run time answers one.
 *
 * <p>The join is what {@link Strings#append} answers, its length checks and its limit included, so a
 * fold of {@code ++} and the run cannot differ because one of them happened at compile time. Where
 * the run ends, there is no text, and none is built here that the run would refuse to build.
 */
public final class JoinedText {

    private JoinedText() {}

    public static Optional<String> of(String a, String b) {
        try {
            return Optional.of(Strings.append(a, b, EvaluationContext.checkpoint()));
        } catch (ConstraintViolation _) {
            return Optional.empty();
        }
    }
}
