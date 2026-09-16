package souther.compiler.query;

import souther.compiler.partition.Generator;

/**
 * What one search of a rule of a decision came to.
 *
 * <p>Two answers and not one. Whether a row is owed at the rule is a question about the model;
 * what composing a row for it came to is a question about this compiler. They are asked by one
 * search because composing is the instrument the first is asked through, and they may not be
 * recorded as one answer: a generator that could not compose is not a rule the model leaves open,
 * and a rule nothing settled is not a generator that fell short. An account folding them writes
 * what this compiler managed into what the model says, which is the one thing the account exists to
 * keep apart.
 *
 * <p><b>Both are held, and neither is read off the other.</b> What the search did used to be a word
 * that was present where the composing fell short and absent otherwise, so its absence stood for a
 * candidate having been composed and for nobody having composed anything at all — and a composing
 * that came to nothing and thereby settled the rule could not be spelled: writing it as the absence
 * said a candidate was produced, and writing it as the word said the rule was unsettled. Whichever
 * was chosen, one of the two axes was being answered from the other.
 *
 * <p>What the pair may be is checked here and nowhere else. Every requirement says which search it
 * is the answer of — the readings settle some rules before anything is composed, a witness is
 * something that was composed, and the words are what a composing that came to nothing said — so a
 * settlement that disagrees with itself is refused where it is made rather than read as either half
 * downstream.
 *
 * @param requirement whether a row is owed at the rule, in the three states ADR-0091 fixes
 * @param search      what composing a row for it came to
 */
public record RuleSettlement(RuleRequirement requirement, RuleSearch search) {

    public RuleSettlement {
        if (requirement == null) {
            throw new IllegalArgumentException("a search of a rule comes to some answer about it");
        }
        if (search == null) {
            throw new IllegalArgumentException("a settlement says what the composing came to");
        }
        // Exhaustive over the requirements, so an answer added is one somebody says the search of
        // rather than one that quietly takes whatever it was given.
        boolean agrees = switch (requirement) {
            // Something was seen standing in it, which is something that was composed.
            case RuleRequirement.Required _ -> search instanceof RuleSearch.Composed;
            // Read off the rules before a search was made, both of them.
            case RuleRequirement.Excluded.OnePositionCannotBeBoth _,
                 RuleRequirement.Excluded.AnArmNothingReaches _ ->
                    search instanceof RuleSearch.NotMade;
            // And the one the composings themselves proved, which is what they came back with.
            case RuleRequirement.Excluded.TheRulesLeaveNoValueForIt _ ->
                    search instanceof RuleSearch.CameToNothing;
            // The inquiry having had no candidate is that same shape without the proof.
            case RuleRequirement.Unsettled.NothingWasComposedToTry _ ->
                    search instanceof RuleSearch.CameToNothing;
            // And the rest are what became of a row that was composed.
            case RuleRequirement.Unsettled.AComposedRowWentElsewhere _,
                 RuleRequirement.Unsettled.CouldNotTellWhereTheRowWent _,
                 RuleRequirement.Unsettled.NothingWatchedTheRow _ ->
                    search instanceof RuleSearch.Composed;
        };
        if (!agrees) {
            throw new IllegalArgumentException(
                    "a rule settled as " + requirement + " by a search that " + search);
        }
    }

    /** A rule the readings settled, which nothing was composed for. */
    public static RuleSettlement read(RuleRequirement.Excluded requirement) {
        return new RuleSettlement(requirement, new RuleSearch.NotMade());
    }

    /** A search that had a candidate to try the rule with, whatever it then settled. */
    public static RuleSettlement of(RuleRequirement requirement) {
        return new RuleSettlement(requirement, new RuleSearch.Composed());
    }

    /** A search whose composing produced no candidate, in the words the composing came back with. */
    public static RuleSettlement nothingToTryWith(Generator.UnresolvedCombination why) {
        if (why == null) {
            throw new IllegalArgumentException("a composing that came to nothing says what of");
        }
        return new RuleSettlement(new RuleRequirement.Unsettled.NothingWasComposedToTry(),
                RuleSearch.CameToNothing.by(why));
    }

    /**
     * A rule every way of standing the dependencies in proved the rules leave no value for, in the
     * words those composings came back with.
     *
     * <p>The universal is the caller's to establish
     * ({@link Adequacy.DecisionSearch#provedByEveryWay}) and is not a claim this value makes: what
     * is held is what each composing said, the way a point holds its searches.
     */
    public static RuleSettlement provedNothingTakesIt(RuleSearch.CameToNothing proofs) {
        return new RuleSettlement(new RuleRequirement.Excluded.TheRulesLeaveNoValueForIt(), proofs);
    }

    /**
     * What the composing fell short on, or null where it did not fall short.
     *
     * <p>A shortfall is a composing that came to nothing without settling anything, which is the
     * one of the three searches a reader can act on by raising what this compiler writes. A
     * composing that proved the rule leaves no value came to nothing and fell short of nothing, and
     * a search nobody made has nothing to say either.
     */
    public Generator.UnresolvedCombination synthesisShortfall() {
        return requirement instanceof RuleRequirement.Unsettled.NothingWasComposedToTry
                && search instanceof RuleSearch.CameToNothing came ? came.only() : null;
    }
}
