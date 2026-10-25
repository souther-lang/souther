package souther.compiler.partition;

import souther.compiler.check.FieldDomains;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Place;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * What one position can take, for a search choosing them one at a time.
 *
 * <p>The rules of every value whose clauses reach a position are read once and handed each settling
 * as it arrives ({@link ConstructionRules#limitsAt}), which is what a settling is: an equality taken
 * onto everything the clauses came to. A search that read the declarations at each position would be
 * arriving at the same state by reading every clause over again.
 *
 * <p><b>What a position can take is kept, and this is where keeping it belongs.</b> A depth-first
 * search reaches one settling by many routes and asks the same position about it at each of them,
 * which is a fact about how the search walks and not about what the rules mean. Kept in the reading,
 * it would be the rules holding a note about a caller that repeats itself; kept here, it is one
 * search's own working.
 *
 * <p>One of these per search. What it holds is true under the value being composed and the caller's
 * fixed positions, and both are settled when it is made.
 */
final class ConditionedCandidates {

    private final RuleReadingContext reading;
    private final ConstructionRules rules;
    private final Map<Asked, List<FixtureTemplate>> found = new HashMap<>();

    /** What of this compiler's building what the positions can take met, over every settling. */
    private CompositionShortfall met = CompositionShortfall.NONE;

    /**
     * @param rules the rules of the value being composed, read once for the whole search
     */
    ConditionedCandidates(RuleReadingContext reading, ConstructionRules rules) {
        this.reading = reading;
        this.rules = rules;
    }

    /**
     * What can stand at {@code position} once {@code settled} is taken on.
     *
     * @param settled the numbers the positions before this one took, where they were written. Never
     *                held on to: what is kept is the part of it the rules naming the position name
     */
    List<FixtureTemplate> at(ConstructionPlan.Slot position, Map<TermPath, Place> settled) {
        Asked asked = new Asked(position.at(), rules.settlingAt(position.at(), settled));
        List<FixtureTemplate> known = found.get(asked);
        if (known != null) {
            return known;
        }
        FieldDomains.ConstructionLimits limits = rules.limitsAt(asked.at(), asked.settled());
        // A position of the plan, which a rule naming something under it would have laid out as
        // positions rather than left to be chosen whole: nothing around is left to hold it to.
        Proposals stands = Witnesses.firstWhatThePlaceAdmits(position.type(), limits,
                reading, Set.of(), Partitions.RulesAround.NONE,
                () -> Partitions.displacedRepresentativesOf(position.type(), reading, limits));
        met = met.and(stands.met());
        found.put(asked, stands.values());
        return stands.values();
    }

    /**
     * What of this compiler's building the values offered so far met, so that a search that
     * chose from them and came back without a row says what its offer was short of.
     */
    CompositionShortfall met() {
        return met;
    }

    /** One position under one settling, which is what the same answer is the answer to. */
    private record Asked(TermPath at, ConstructionRules.Settling settled) {}
}
