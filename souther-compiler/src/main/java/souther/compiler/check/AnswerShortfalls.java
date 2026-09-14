package souther.compiler.check;

import souther.compiler.values.UnreadReason;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Set;

/**
 * What the answer a position waited for was short of, which no rule is answerable for.
 *
 * <p>The other half of what a question stands on. An allowance run down by everything a position
 * admits is a fact about what the rules come to and about none of them
 * ({@link UnreadReason.About#THE_ANSWER}), so it is held at the position and every rule whose
 * question waited on that answer stands on it. Read as a rule's, an author is told to rewrite a form
 * nothing complained of, and the position is as wide as it was however the form is written.
 *
 * <p><b>No written place, and so no order.</b> A shortfall of a rule says the place an author wrote
 * ({@link RuleShortfall}); this has none to say, because the thing it is about is what the rules
 * come to together and nobody wrote that anywhere. A carrier giving one of these a place — or an
 * order among them, which is the same claim made smaller — would be answering where in a source a
 * reader should look for something the source does not hold.
 *
 * @param reasons what the answer was short of, each a fact about the answer and about no rule
 */
record AnswerShortfalls(Set<UnreadReason> reasons) {

    AnswerShortfalls {
        if (reasons == null) {
            throw new IllegalArgumentException("an account of an answer says what it was short of");
        }
        reasons.forEach(each -> {
            if (each.about() != UnreadReason.About.THE_ANSWER) {
                throw new IllegalArgumentException(
                        "a reason about " + each.about() + " is not one the answer is short of: "
                                + each);
            }
        });
        reasons = Collections.unmodifiableSet(new LinkedHashSet<>(reasons));
    }

    /** Nothing, which is what a question standing on its rule alone has here. */
    static AnswerShortfalls none() {
        return new AnswerShortfalls(Set.of());
    }

    /** Whether the answer was short of nothing. */
    boolean isEmpty() {
        return reasons.isEmpty();
    }
}
