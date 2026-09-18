package souther.compiler.check;

import souther.compiler.types.TypeKey;

/**
 * What a lookup says about one declaration, for a reader in another module.
 *
 * <p>Three answers and not two, for the reason {@link ExpandedClauseResult} has three. A
 * declaration nothing declares and a declaration whose module could not be read are opposite facts
 * and one absence: the first carries no rule for a value to be short of, and the second carries
 * whatever its author wrote. A reader handed the absence alone cannot tell them apart, and the one
 * that has to tell them apart asks somewhere else — which is a second authority answering half of
 * what this one was asked.
 *
 * <p>Beside {@link DeclarationMeaning} and not inside it. What a declaration says is the
 * declaration's; whether there is one to say anything, and whether this compilation got far enough
 * to find out, are facts about the lookup. An arm of the meaning for either would be a meaning
 * every reader of what a declaration states would have to carry a case for.
 */
public sealed interface PublishedDeclarationResult {

    /** What the declaration says. */
    record Found(DeclarationMeaning said) implements PublishedDeclarationResult {

        public Found {
            if (said == null) {
                throw new IllegalArgumentException("a found answer is what a declaration says");
            }
        }
    }

    /**
     * The declaration exists and what it says could not be worked out — its module does not
     * compile, its imports form a cycle, or settling it failed.
     *
     * <p>Never widened to a declaration that says nothing. A reading turns this into the rule it
     * already has a word for, that not every rule governing the value was reached; read as a
     * declaration with no rules, the same value would be held to nothing and nothing would say so.
     */
    record Unavailable(TypeKey declaration) implements PublishedDeclarationResult {}

    /** Nothing in this compilation declares one, and the language does not either. */
    record NotDeclared(TypeKey declaration) implements PublishedDeclarationResult {}
}
