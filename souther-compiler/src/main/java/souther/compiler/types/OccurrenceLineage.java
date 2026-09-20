package souther.compiler.types;

import souther.compiler.RecordOfTheBuilding;

/**
 * Which copy of a body a construct stands in, said as everything that made the copy, in the order
 * it did.
 *
 * <p>A written construct stands more than once in the tree that runs, and two things make it so. A
 * helper is spliced into each call of it, which is a copy made by a call ({@link ExpansionLineage});
 * and a value named on paths that share no region is built once per region, which is a copy made by
 * a region ({@link MaterialisationSite}). Neither implies the other and they nest either way: a
 * value's body may call a helper, a helper's body may name a value, and a value may name a value
 * inside a fork of its own body. What tells one such copy from another is the whole chain, in the
 * order the copies were made, so it is one chain and not a pair of them.
 *
 * <p><b>Provenance and not position.</b> The chain answers how this instance of a construct came to
 * exist. Every construct inside one build of a value carries the same chain, so it never says where
 * in the body a construct is.
 *
 * <p><b>The model reads a part of it.</b> A model states what a call spliced in, and what the
 * sharing policy did about a value is not the model's: {@link #expansionProjection} is the chain
 * without the builds, which is what {@link ModelOccurrence} and a block's crossing read. The
 * projection is derived and never held beside this, so the two cannot come apart.
 *
 * <p>Each kind of step is well founded for a reason of its own, and this claims neither. A call
 * cannot be its own expansion because a declaration that can reach itself is left standing
 * ({@link souther.compiler.check.HelperGraph#recurses}); a value cannot be its own build because a
 * module whose values are not well founded is refused before a body of it is expanded. What each
 * step's subsystem guarantees is that subsystem's to say.
 */
public sealed interface OccurrenceLineage extends RecordOfTheBuilding {

    /** The construct as the source wrote it, in the one build of the body that wrote it. */
    OccurrenceLineage ORIGINAL = new Original();

    /** A construct no copy stands between. */
    record Original() implements OccurrenceLineage {

        @Override
        public ExpansionLineage expansionProjection() {
            return ExpansionLineage.ORIGINAL;
        }

        @Override
        public String toString() {
            return "as written";
        }
    }

    /**
     * A copy of {@code expanded}'s body, made at {@code at}, inside {@code within}.
     *
     * <p>The same three things an {@link ExpansionLineage.Expansion} holds, for the same reasons.
     */
    record Expansion(OccurrenceLineage within, ValueName expanded, ExpansionSite at)
            implements OccurrenceLineage {

        public Expansion {
            if (within == null || expanded == null || at == null) {
                throw new IllegalArgumentException(
                        "a copy is of something, at some site, inside something: " + expanded
                                + " at " + at + " in " + within);
            }
        }

        @Override
        public ExpansionLineage expansionProjection() {
            return within.expansionProjection().copiedInto(expanded, at);
        }

        @Override
        public String toString() {
            return within + " / " + expanded + " @ " + at;
        }
    }

    /**
     * One build of {@code materialised}'s body, for the region {@code at} names, inside
     * {@code within}.
     *
     * <p>Beside the site, what was built. Two values named in one region are two builds there, and
     * an expansion likewise says what it copied as well as where.
     *
     * @param within       which copy the region itself stands in, so that one region reached in two
     *                     copies of its body is two builds
     * @param materialised what was built
     * @param at           the region it was built for
     */
    record Materialisation(OccurrenceLineage within, ValueName materialised,
                           MaterialisationSite at) implements OccurrenceLineage {

        public Materialisation {
            if (within == null || materialised == null || at == null) {
                throw new IllegalArgumentException(
                        "a build is of something, for some region, inside something: "
                                + materialised + " for " + at + " in " + within);
            }
        }

        @Override
        public ExpansionLineage expansionProjection() {
            return within.expansionProjection();
        }

        @Override
        public String toString() {
            return within + " / built " + materialised + " @ " + at;
        }
    }

    /**
     * This chain read as the calls it went through alone: every build dropped, every copy kept in
     * the order it was made.
     */
    ExpansionLineage expansionProjection();

    /** This lineage with one more copy made by a call. */
    default Expansion copiedInto(ValueName expanded, ExpansionSite at) {
        return new Expansion(this, expanded, at);
    }

    /** This lineage with one more build of a value for a region. */
    default Materialisation builtFor(ValueName materialised, MaterialisationSite at) {
        return new Materialisation(this, materialised, at);
    }
}
