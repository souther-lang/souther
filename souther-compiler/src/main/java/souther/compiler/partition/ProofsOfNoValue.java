package souther.compiler.partition;

import souther.compiler.inputs.SearchRegion;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.Map;

/**
 * What {@link StandingImpossibility} answered, by the region and by the question it was asked.
 *
 * <p>A proof is a function of the two and nothing else, so what is kept here is the answer to a
 * question and not a memory of a search: asked again, the proof comes back as it did, and nothing a
 * search offered or tried is held.
 *
 * <p>The question is {@link StandingImpossibility.Asked}, which is what the proof reads of a
 * standing and no more. Keyed by the standing, an answer would be told apart by whatever else a
 * standing carries — the space its levels are written in is made again each time the item is asked
 * for its standing — and the same proof would be made for each of them. A standing nothing is proved
 * of has no question, so nothing is kept for it.
 *
 * <p>A region is told apart by identity, because narrowing one makes another and the answers of the
 * first say nothing of it. {@code false} is kept as well: it is the answer that the question did not
 * settle, and asking again does not settle it.
 *
 * <p>Held for as long as its owner is, which is what bounds it: it holds the regions that were asked
 * about and lets go of them when the owner does.
 */
final class ProofsOfNoValue {

    /** Made when the first question is kept, so an owner asked nothing it can prove holds no table. */
    private Map<SearchRegion, Map<StandingImpossibility.Asked, Boolean>> answers;

    /** Whether the region leaves the standing's quantity no value the item asks for. */
    boolean provesImpossible(SearchRegion region, Standing standing) {
        StandingImpossibility.Asked asked = StandingImpossibility.askedBy(standing);
        if (asked == null) {
            return false;
        }
        if (answers == null) {
            answers = new IdentityHashMap<>();
        }
        Map<StandingImpossibility.Asked, Boolean> ofTheRegion =
                answers.computeIfAbsent(region, _ -> new HashMap<>());
        Boolean had = ofTheRegion.get(asked);
        if (had != null) {
            return had;
        }
        boolean proved = StandingImpossibility.provesImpossible(region, asked);
        ofTheRegion.put(asked, proved);
        return proved;
    }
}
