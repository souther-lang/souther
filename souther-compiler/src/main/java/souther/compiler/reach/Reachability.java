package souther.compiler.reach;

/**
 * Whether anything arrives at one place in a body.
 *
 * <p>Three answers, and the third is not a weaker second. A reading that took the conditions in and
 * found no contradiction has shown that <em>this reading</em> found none: an over-approximation
 * coming out empty proves nothing arrives, and the same approximation coming out non-empty proves
 * only that the domains had no word for whatever would have refuted it. Written as two answers, the
 * second of them says both "something arrives" and "nothing here could tell", and every consumer
 * then picks whichever of the two it happens to need.
 *
 * <p><b>Whoever decides a policy reads this and nothing inside it.</b> {@link Proof},
 * {@link Witness} and {@link WhyUnsettled} are payload — a renderer takes one apart to write a
 * sentence, and nothing else does. That is what keeps a domain added to the reading, or a reason
 * added to a proof, from being a change to what an obligation or a claim comes to.
 *
 * <pre>
 *                   obligation      a dead branch      an `unreachable` the author wrote
 *   Unreachable     taken out       warned about       borne out
 *   Reachable       left standing   nothing said       refuted
 *   Unsettled       left standing   nothing said       neither
 * </pre>
 *
 * <p>The two columns on the right are why this is not a boolean. Taking an obligation out and
 * reporting a defect are both owed a proof, and what they do without one differs: one leaves work
 * for an author to do, the other says nothing at all. A single {@code false} cannot tell a reader
 * which of those two nothings it is in.
 */
public sealed interface Reachability {

    /**
     * Nothing arrives here, and {@code proof} is how that was shown.
     *
     * <p>Sound wherever the values the reading worked over are as wide as the ones that can really
     * arrive: a set disjoint from a superset is disjoint from the set. That is the one direction
     * claimed, and both readers of this rest on the same claim.
     */
    record Unreachable(Proof proof) implements Reachability {

        public Unreachable {
            if (proof == null) {
                throw new IllegalArgumentException("nothing arrives here for no reason");
            }
        }
    }

    /**
     * Something arrives here, and {@code witness} is what says so.
     *
     * <p>Not the complement of {@link Unreachable}. There are three ways to earn this and none of
     * them is "the reading found no contradiction": a value that reaches it, a run that went
     * through it, or a rule that states it settles the question completely. Anything else is
     * {@link Unsettled}, because the reader that acts on this refutes something the author wrote,
     * and refuting on a domain's silence is a false report about a correct model.
     */
    record Reachable(Witness witness) implements Reachability {

        public Reachable {
            if (witness == null) {
                throw new IllegalArgumentException(
                        "something arrives here with nothing to show it does");
            }
        }
    }

    /** Nothing settled it. The place keeps whatever it was owed and nothing is said about it. */
    record Unsettled(WhyUnsettled why) implements Reachability {

        public Unsettled {
            if (why == null) {
                throw new IllegalArgumentException("a reading unsettled by nothing settled it");
            }
        }
    }
}
