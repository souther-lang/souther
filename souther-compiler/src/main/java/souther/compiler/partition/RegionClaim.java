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
 * @param basis         what a row here is owed for, which is part of the point's identity
 * @param contributions what settled that at this end, which is not. One end's worth of what the
 *                      point is owed to, since the line the region lies beside settled it as well
 */
public record RegionClaim(RegionBasis basis, PointContributions contributions) {

    public RegionClaim {
        if (basis == null || contributions == null) {
            throw new IllegalArgumentException(
                    "a claim is something owed for, settled by something: " + basis + " "
                            + contributions);
        }
    }

    /**
     * The same claims with one entry per basis, each carrying everything that settled it.
     *
     * <p>A basis is what a row is owed for, so two claims of one basis are one obligation however
     * many things put it there: one end the rules leave, arrived at with one declaration named as
     * having taken it in and again with another, is one end owed to both of them.
     *
     * <p><b>Not two things that stop the run in one place.</b> A line and an end the rules leave can
     * fall together and each stops the run there without the other, so they are two bases and two
     * obligations — which is what the far side of a run is told apart by. Only claims that are the
     * same basis are brought together here.
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
                        out.get(at).contributions().and(each.contributions())));
            }
        }
        return List.copyOf(out);
    }
}
