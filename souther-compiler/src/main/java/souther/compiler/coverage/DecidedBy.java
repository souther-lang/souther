package souther.compiler.coverage;

import souther.compiler.types.BindingOwner;

import java.util.List;

/**
 * What settles which rule one occurrence of a fork decides by.
 *
 * <p>{@link DecisionSources} says who owns the rule; this says, for this copy of the fork, which
 * rule that came to. Together they are what one obligation is: a fork the declaration decides is one
 * obligation however many bodies it was spliced into, and a fork the caller decides is one per rule
 * the caller supplied.
 *
 * <p>Compared and never read for what it says. Nothing here describes a rule — describing one is
 * what cannot tell an argument from a decision, since after expansion both are just an expression
 * standing where a parameter was.
 */
public sealed interface DecidedBy {

    /**
     * Whether an occurrence this settles can be told from another.
     *
     * <p>True for both answers this can give. False only for {@link NotSaid}, whose occurrences are
     * counted as one without anything having established that they are one.
     */
    boolean isSettled();

    /** The declaration decides, so every copy of the fork is one obligation. */
    record ByTheDeclaration() implements DecidedBy {

        @Override
        public boolean isSettled() {
            return true;
        }
    }

    /**
     * The caller decides, with the rules it wrote expanded here.
     *
     * <p>The expansions and not a description of what they hold. An expansion is made once per rule
     * supplied at a call site, so two calls handing in two rules have two of them and a rule handed
     * on through a helper keeps the one it was written as. What this cannot yet tell apart is one
     * rule named at two call sites: each supply is its own expansion, so the two are counted as two
     * obligations — which asks for a row that establishes nothing rather than passing over one that
     * does.
     */
    record BySupplied(List<BindingOwner> rules) implements DecidedBy {

        public BySupplied {
            rules = List.copyOf(rules);
            if (rules.isEmpty()) {
                throw new IllegalArgumentException("a supplied rule is something that was supplied");
            }
        }

        @Override
        public boolean isSettled() {
            return true;
        }
    }

    /**
     * The declaration says the caller decides and nothing here says which rule it handed in.
     *
     * <p>Its own answer and not either of the others. Read as {@link ByTheDeclaration}, copies
     * deciding by two rules are counted as one and a rule nothing exercised is reported as covered;
     * read as a rule of its own, an author is asked for rows that establish nothing. What is owed is
     * that this obligation cannot be judged, which is a fact about this obligation and says nothing
     * about the ones beside it.
     */
    record NotSaid() implements DecidedBy {

        @Override
        public boolean isSettled() {
            return false;
        }
    }

    /** The one {@link ByTheDeclaration}, which carries nothing to tell instances apart. */
    DecidedBy THE_DECLARATION = new ByTheDeclaration();

    /** The one {@link NotSaid}. */
    DecidedBy NOT_SAID = new NotSaid();
}
