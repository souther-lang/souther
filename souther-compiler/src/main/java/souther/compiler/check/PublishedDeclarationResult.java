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
     * A module wrote the declaration and what it says could not be worked out — its module does not
     * compile, its imports form a ring, or settling it failed.
     *
     * <p>Never widened to a declaration that says nothing. A reading turns this into the rule it
     * already has a word for, that not every rule governing the value was reached; read as a
     * declaration with no rules, the same value would be held to nothing and nothing would say so.
     */
    record Unavailable(TypeKey declaration) implements PublishedDeclarationResult {}

    /**
     * No module of this compilation writes one, and the language declares none either.
     *
     * <p>Asked of what the modules were parsed as, and not of anything that resolves. Every answer
     * from resolution down is cut for a module whose imports form a ring, so read there a
     * declaration nobody could reach would be one nobody wrote — which is the arm above collapsing
     * into this one, at the rung below the one this type exists to keep apart.
     *
     * <p>The lookup of expanded clauses tells its own two apart by the same question, which is what
     * keeps a value from being short of its rules to one reader and held to none by the other
     * ({@code TheTwoBoundariesTellUnavailableFromNotDeclaredAlikeTest}). Only those two: whether
     * either has an answer at all is each one's own question, and a form with no rule to write has
     * clauses to hand over whatever became of the module that holds it.
     */
    record NotDeclared(TypeKey declaration) implements PublishedDeclarationResult {}
}
