package souther.compiler.types;

import java.util.ArrayList;
import java.util.List;

/**
 * One step of the way a construct came to stand where it does in the tree that runs: a copy made at
 * a call, or a build of a value made for a region.
 *
 * <p>The steps and not what any surface says of them. A document writes them as fields and a page
 * as words, and each reads them off one list made here — two walks of a lineage would be free to
 * keep different steps, and then the document and the page would be naming two different copies of
 * one construct.
 *
 * <p>Every step is kept, with what tells it from its neighbours. A copy is told by the site it was
 * made at and a build by the region it was made for; a surface that can say no more than which
 * value was copied still holds which copy it was.
 */
public sealed interface StepOfACopy {

    /**
     * A copy of {@code called}'s body, made at {@code at}.
     *
     * @param called what was copied
     * @param at     where the copy was made: a call the author wrote, a name written where a value
     *               goes, or a block handed over and applied
     */
    record ACall(ValueName called, ExpansionSite at) implements StepOfACopy {

        public ACall {
            if (called == null || at == null) {
                throw new IllegalArgumentException("a copy is of something, made somewhere: "
                        + called + " at " + at);
            }
        }
    }

    /**
     * A build of {@code built}, made for {@code at}.
     *
     * <p>One build of a value among the builds this compilation made of it, and nothing the model
     * states: the model names the value once wherever it is built.
     *
     * @param built what was built
     * @param at    the region it was built for
     */
    record ABuild(ValueName built, MaterialisationSite at) implements StepOfACopy {

        public ABuild {
            if (built == null || at == null) {
                throw new IllegalArgumentException("a build is of something, for some region: "
                        + built + " for " + at);
            }
        }
    }

    /** Every step of {@code lineage}, outermost first, and none where it is as written. */
    static List<StepOfACopy> of(OccurrenceLineage lineage) {
        List<StepOfACopy> out = new ArrayList<>();
        for (OccurrenceLineage at = lineage; !(at instanceof OccurrenceLineage.Original); ) {
            switch (at) {
                case OccurrenceLineage.Expansion copy -> {
                    out.add(new ACall(copy.expanded(), copy.at()));
                    at = copy.within();
                }
                case OccurrenceLineage.Materialisation build -> {
                    out.add(new ABuild(build.materialised(), build.at()));
                    at = build.within();
                }
                case OccurrenceLineage.Original original -> at = original;
            }
        }
        return out.reversed();
    }

    /** The calls of {@code lineage}, outermost first: a lineage of the model holds no builds. */
    static List<StepOfACopy> of(ExpansionLineage lineage) {
        List<StepOfACopy> out = new ArrayList<>();
        for (ExpansionLineage at = lineage; at instanceof ExpansionLineage.Expansion copy;
                at = copy.within()) {
            out.add(new ACall(copy.expanded(), copy.at()));
        }
        return out.reversed();
    }
}
