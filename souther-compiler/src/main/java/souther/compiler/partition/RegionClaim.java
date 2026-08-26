package souther.compiler.partition;

import java.util.ArrayList;
import java.util.List;

/**
 * One thing a row in a region is owed for, and who can move it.
 *
 * <p>The two together, from the reading that worked the region out. Which of them a row answers for
 * is what tells one region point from another ({@link RegionBasis}); who can move what settled it is
 * what says whose account the point falls in, and it is no part of which point this is. Held apart
 * in two places instead, a reader would have to put them back together by whatever they had in
 * common, and what they have in common is where they were read.
 *
 * @param basis       what a row here is owed for, which is part of the point's identity
 * @param attribution who settled that, which is not
 */
public record RegionClaim(RegionBasis basis, PointAttribution attribution) {

    public RegionClaim {
        if (basis == null || attribution == null) {
            throw new IllegalArgumentException(
                    "a claim is something owed for, by somebody: " + basis + " " + attribution);
        }
    }

    /**
     * The same claims with one entry per basis, each carrying everything that settled it.
     *
     * <p>A basis is what a row is owed for, so two claims of one basis are one thing to write a row
     * for however many things put it there — an end a line and a declaration's narrowing both stop
     * the quantity at is one end. Kept as two, the region would be owed twice for one place.
     */
    public static List<RegionClaim> byBasis(List<RegionClaim> claims) {
        List<RegionClaim> out = new ArrayList<>();
        for (RegionClaim each : claims) {
            int at = -1;
            for (int i = 0; i < out.size(); i++) {
                if (out.get(i).basis().equals(each.basis())) {
                    at = i;
                    break;
                }
            }
            if (at < 0) {
                out.add(each);
            } else {
                out.set(at, new RegionClaim(each.basis(),
                        out.get(at).attribution().and(each.attribution())));
            }
        }
        return List.copyOf(out);
    }
}
