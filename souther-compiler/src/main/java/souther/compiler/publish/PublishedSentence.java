package souther.compiler.publish;

import souther.compiler.diag.msg.Message;
import souther.compiler.diag.msg.ReportMessage;
import souther.compiler.diag.msg.SearchMessage;

/**
 * What a field of a document says, for the fields that sometimes say it about a rule.
 *
 * <p>A sum and not a string, because whether a handle is in there is what the schema says of the
 * field and what a reader acts on. Handed the finished words, a field could carry a sentence with a
 * handle spelled by whoever built it — which is the shape this whole issue is about, one layer down:
 * the sentence would be right today and free to come apart from the one every other field writes.
 *
 * <p>So the handle is handed over as a handle and the words around it as words, and what puts them
 * together is {@link RuleHandleSurface}. A field that carries one is then a field that carries one
 * because there was no way to write it otherwise.
 */
public sealed interface PublishedSentence {

    /** Words about something that is not a rule — a class, an arm, a case of an input. */
    record Words(String said) implements PublishedSentence {

        public Words {
            if (said == null || said.isEmpty()) {
                throw new IllegalArgumentException("a field a document writes says something");
            }
        }
    }

    /**
     * A rule handle with words of the field's own around it.
     *
     * <p>The words are a sentence the handle is put into, and not a string before it and a string
     * after it: where the handle stands in the sentence is the language's, and a language that
     * names the rule before the point of it has no words to put in front.
     */
    record AroundAHandle(PublishedRuleHandle handle, Around around) implements PublishedSentence {

        public AroundAHandle {
            if (handle == null || around == null) {
                throw new IllegalArgumentException("a sentence about a rule is a handle and the"
                        + " words around it: " + handle + " " + around);
            }
        }

        /** The handle by itself, for a field whose whole sentence it is. */
        public static AroundAHandle alone(PublishedRuleHandle handle) {
            return new AroundAHandle(handle, new Around.Alone());
        }
    }

    /** The sentences a handle is said in, each with the handle's words as a value. */
    sealed interface Around {

        /** The sentence, with {@code handle} the rule's words. */
        Message with(String handle);

        /** The handle and nothing else. */
        record Alone() implements Around {
            @Override
            public Message with(String handle) {
                return new ReportMessage.Verbatim(handle);
            }
        }

        /** A point of the line the rule draws, by its role. */
        record PointOf(String role) implements Around {
            @Override
            public Message with(String handle) {
                return new ReportMessage.DeclaredPointOf(role, handle);
            }
        }

        /** The rule as the declarations that took an end of its line in narrowed it. */
        record Within(SearchMessage declarations) implements Around {
            @Override
            public Message with(String handle) {
                return new SearchMessage.RuleWithin(new SearchMessage.TheRuleCited(handle),
                        declarations);
            }
        }

        /** The rule and what was asked of it that nothing answered. */
        record ThenAsked(Message asked) implements Around {
            @Override
            public Message with(String handle) {
                return new ReportMessage.RuleThenAsked(handle, asked);
            }
        }
    }
}
