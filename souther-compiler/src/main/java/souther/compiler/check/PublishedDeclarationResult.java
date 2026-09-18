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
     * The name resolves to a declaration and what it says could not be worked out.
     *
     * <p>Never widened to a declaration that says nothing. A reading turns this into the rule it
     * already has a word for, that not every rule governing the value was reached; read as a
     * declaration with no rules, the same value would be held to nothing and nothing would say so.
     */
    record Unavailable(TypeKey declaration) implements PublishedDeclarationResult {}

    /**
     * The name does not resolve to a declaration of this compilation, and the language declares
     * none either.
     *
     * <p>Which is a wider answer than a name nobody wrote. Whether a name resolves to a declaration
     * is read from the resolution that fails when a module does — so a module whose imports form a
     * ring, or that does not parse, has the declarations it writes answered for here as
     * declarations there are none of. The expanded side divides the cases by the same question and
     * answers alike, which {@code TheTwoBoundariesPutADeclarationInTheSameArmTest} holds. What
     * keeps this from being read as a value held to nothing is that a compilation in that state has
     * no reading of the importing module either.
     */
    record NotDeclared(TypeKey declaration) implements PublishedDeclarationResult {}
}
