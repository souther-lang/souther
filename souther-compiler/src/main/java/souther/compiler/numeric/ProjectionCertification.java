package souther.compiler.numeric;

/**
 * What came of trying to establish that each position's box is the whole of what the rules leave it.
 *
 * <p>A certificate or the reason there is none, and both are the algebra's answer. Handed back as
 * the certificate alone, the reason was dropped at the boundary and worked out again on the other
 * side of it from what was left over — which reports the wrong one wherever two things are in the
 * way at once, and reports whichever one the elimination happens to end at when something new is.
 *
 * <p>None of the three refusals is the box being wider than the rules. Each is a hypothesis that
 * was not met or a proof that did not come, and what a reader may do with any of them is decline to
 * promise an edge.
 *
 * <p>Asked in an order, because one of them settles the others. Where nothing is left there is no
 * box to be the whole of anything, and listing what else could not be shown about a value nobody can
 * build gives an author nothing to do. The other two stand together: a rule the proof could not
 * reach is named by the reading that handed it over, so a value can come back spaced unalike and
 * still have every rule it could not state written down beside it.
 */
public sealed interface ProjectionCertification {

    /** Something established it, and what. */
    record Certified(ProjectionCertificate by) implements ProjectionCertification {

        public Certified {
            if (by == null) {
                throw new IllegalArgumentException("certified by something, or not certified");
            }
        }
    }

    /**
     * The rules leave no value at all, so there is no box for anything to be the whole of.
     *
     * <p>Said rather than let pass. Every rule follows from an emptiness, so a value nobody can
     * build would otherwise come back with every rule proven and every end of it promised.
     */
    record NothingIsLeft() implements ProjectionCertification {}

    /**
     * The rules relate positions whose values are spaced differently.
     *
     * <p>The hypothesis of the theorem that carries a system to one of its ranges — see
     * {@link ProjectionCertificate.ByBoxAndClosedDifferences}. Not something wrong with the rules,
     * and not a rule this could not prove: it is about which theorem applies.
     */
    record PositionsSpacedDifferently() implements ProjectionCertification {}

    /**
     * Some rule did not follow from what was derived.
     *
     * <p>Which rule is not said here. What the algebra holds is the rules as it read them, and the
     * name an author would recognise belongs to the reading that handed them over — so the one that
     * can say it says it, and this says only that there was one.
     */
    record NotEveryRuleIsProven() implements ProjectionCertification {}

    /** The certificate, where there is one. */
    default ProjectionCertificate certificate() {
        return this instanceof Certified it ? it.by() : null;
    }
}
