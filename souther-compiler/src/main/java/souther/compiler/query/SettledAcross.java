package souther.compiler.query;

import java.util.List;

/**
 * What a rule of a decision came to over every place it is stated at.
 *
 * <p>One requirement and as many searches as answer it. Whether a row is owed at the rule is one
 * answer, over all of its places at once: a row taking the rule at any place takes it, and the model
 * leaves it no row only where it leaves every place none. What each search came to and went without
 * is not one answer — each place is searched along its own way, and what one met is not what
 * another met. Held as the one place that answered best, the rest were dropped, and a figure that
 * stopped the search at a second call of a helper reached nobody.
 *
 * <p>So the places held are the ones that answer the rule, the one the requirement is read off
 * first:
 *
 * <ul>
 * <li>a place something stood in, alone — the row there settles the rule, and nothing the other
 *     places came to is owed a reader;
 * <li>every place, where the model leaves each of them no row, each with what left it none;
 * <li>otherwise every place the model leaves open, the one that established the most first and the
 *     rest after it in the order they were stated. A place the model leaves no row is not where an
 *     author could write one, and is left out.
 * </ul>
 *
 * <p>Checked here, so that no reader has to ask which of these it was handed.
 *
 * @param places the places that answer the rule, the one the requirement is read off first
 */
public record SettledAcross(List<SettledAt> places) {

    public SettledAcross {
        places = List.copyOf(places);
        if (places.isEmpty()) {
            throw new IllegalArgumentException("a rule settled somewhere was settled at a place");
        }
        RuleRequirement first = places.getFirst().settlement().requirement();
        boolean agrees = switch (first) {
            case RuleRequirement.Required _ -> places.size() == 1;
            case RuleRequirement.Excluded _ -> places.stream().allMatch(each ->
                    each.settlement().requirement() instanceof RuleRequirement.Excluded);
            case RuleRequirement.Unsettled _ -> places.stream().allMatch(each ->
                    each.settlement().requirement() instanceof RuleRequirement.Unsettled);
        };
        if (!agrees) {
            throw new IllegalArgumentException("the places answering a rule " + first
                    + " are the ones that answer it so: " + places);
        }
    }

    /** The place the rule's requirement was read off. */
    public SettledAt answer() {
        return places.getFirst();
    }

    /** Whether a row is owed at the rule, over all of its places. */
    public RuleRequirement requirement() {
        return answer().settlement().requirement();
    }
}
