package souther.compiler.check;

import souther.compiler.diag.Citation;
import souther.compiler.diag.SourceNameResolver;
import souther.compiler.source.SourceId;

/**
 * How a reader finds the rule a question is about.
 *
 * <p>A projection of {@link RuleRef} for a document to print, and never an identity. Two rules are
 * the same rule when their {@code RuleRef}s are equal; what this adds is a handle an author can act
 * on, which is not the same thing and must not become a key — a rule written once and read twice is
 * one rule, and a rule and the handle for it are not in step wherever a name is absent.
 *
 * <p>Two answers, because rules are found two ways. An author names a clause of an invariant and
 * looks it up by that name; a comparison in a body has no name and is found where it is written. A
 * single string over both would have to spell a place as a name, and {@link RuleRef#named} says why
 * that is wrong for the one that has none: a comparison is written rather than named.
 *
 * <p><b>Not {@link souther.compiler.partition.LineOrigin}.</b> That says where a rule was read, and
 * one rule read in two calls of a helper has two of them — so putting it here would make a document
 * choose which reading to show for a question the model raised once. This says where the rule was
 * written, which is the rule's own and is one however often it is read.
 */
public sealed interface RuleCitation {

    /**
     * How a reader finds a rule the author wrote a name beside.
     *
     * <p>Two overloads and no {@code RuleRef} one, which is the point. {@link RuleRef#named} answers
     * for a comparison too — with what it is rather than what it is called — and a total factory
     * over {@code RuleRef} would hand that back as a name, sending an author to look for a clause
     * called {@code the comparison}. Nothing in {@link Named} would refuse it: the string is not
     * empty. A comparison is found by {@link WrittenAt}, from where it is written, which is a place
     * this could not invent.
     */
    static Named named(RuleRef.Invariant rule) {
        return new Named(rule.named());
    }

    /** The same, of a clause of an {@code ensures}. */
    static Named named(RuleRef.Ensures rule) {
        return new Named(rule.named());
    }

    /** The name the author gave it, as a report writes the rule. */
    record Named(String name) implements RuleCitation {

        public Named {
            if (name == null || name.isEmpty()) {
                throw new IllegalArgumentException("a rule called nothing is cited by where it is");
            }
        }
    }

    /**
     * Where the author wrote it, for a rule that has no name.
     *
     * <p>{@link Citation} and not a bare position, because where a rule is written and where a
     * reader is standing are not always the same file: a comparison inside a helper is written
     * there and reached from the call, and the same type says both.
     */
    record WrittenAt(Citation at) implements RuleCitation {

        public WrittenAt {
            if (at == null) {
                throw new IllegalArgumentException("a rule with no name is found by where it is");
            }
        }
    }

    /**
     * How a report writes this, where it knows what to call a source.
     *
     * <p>The one formatter, shared with the borders a comparison draws — a rule and a line the same
     * rule drew are found the same way, and two spellings of one place would read as two places.
     * What is not shared is an identity: where a rule was read is
     * {@link souther.compiler.partition.LineOrigin}'s and one rule has as many of those as it has
     * readings.
     */
    default String said(SourceNameResolver names, SourceId sectionSource) {
        return switch (this) {
            case Named named -> named.name();
            // Written here, and reached from somewhere else: a comparison inside a helper is one
            // rule and a reader is sent to two places, which the citation already tells apart.
            case WrittenAt written -> WHAT_IT_IS
                    + joining(written.at()) + written.at().said(names, sectionSource);
        };
    }

    /**
     * What goes between the construct and the place.
     *
     * <p>Shared with the borders the same rule drew, which is the whole of what those two have in
     * common: a word, and how it joins to a place. Neither holds the other's identity.
     */
    static String joining(Citation at) {
        return at instanceof Citation.Elsewhere ? " in " : "@";
    }

    /**
     * What a report calls a rule that has no name, which is one word.
     *
     * <p>One word because there is one thing to say. This was the construct the comparison stood
     * in, which is not the rule: a condition holds as many rules as it holds comparisons, so
     * {@code guard} was one word for all of them — and a comparison given a name a line above the
     * fork that tests it is the same rule with no fork over it to take a word from.
     *
     * <p>English, like every other word a report writes from a rule. What a diagnostic says instead
     * is chosen in the reader's language, from the same fact.
     */
    String WHAT_IT_IS = "comparison";
}
