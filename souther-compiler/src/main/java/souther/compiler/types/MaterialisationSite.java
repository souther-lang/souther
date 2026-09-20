package souther.compiler.types;

import souther.compiler.SettledAnswer;

/**
 * Why two materialisations of one value in one copy of a body are two, said in words the source
 * settles.
 *
 * <p>A value denotes as if its body stood at each reference, and an implementation may share one
 * materialisation among the references inside one evaluation region. Where a value is named on
 * paths that share no region it is materialised more than once, and what tells those
 * builds apart is the reason a second one was needed: the region each of them stands for.
 *
 * <p><b>Not where a construct stands.</b> Every construct inside one materialisation shares the
 * site, so this says which build of the value a construct is part of and nothing about where in the
 * value it is. It is the region that made the build, named by what the author wrote around it.
 *
 * <p><b>Not how the compiler chose to share.</b> Which sites there are follows the sharing policy,
 * and a different policy would make different ones. What a site must do holds under any policy: be
 * a function of what the source settled, and tell apart two builds that a derivation makes. A
 * walk's count, the binder a pass minted for a build and the reference that asked for it first are
 * all out, each moves with how the compiler ran.
 *
 * <p>The regions a body's own {@code Hir.Expansion} opens are not sites. Entering another body's
 * copy is a step of the lineage ({@link OccurrenceLineage.Expansion}) and opens no region of its
 * own: what it names is demanded by the region it stands in.
 */
public sealed interface MaterialisationSite extends SettledAnswer {

    /**
     * The region a definition's body is the whole of.
     *
     * <p>A definition names it and not a bare "root": two behaviors that each name one value are two
     * builds of it, and nothing else says which body they were made for.
     */
    record Body(WrittenOwner.Body owner) implements MaterialisationSite {

        public Body {
            if (owner == null) {
                throw new IllegalArgumentException("a body is some definition's: " + owner);
            }
        }
    }

    /**
     * A region a fork, a short-circuit or a comprehension the author wrote opens.
     *
     * @param construct which construct it is, in the words the source counted it by
     * @param slot      which of the regions that construct opens
     */
    record Slot(SourceConstructOrigin construct, RegionSlot slot) implements MaterialisationSite {

        public Slot {
            if (construct == null || !construct.isWritten() || slot == null) {
                throw new IllegalArgumentException(
                        "a region of a construct the source wrote: " + construct + " at " + slot);
            }
        }
    }

    /**
     * The body of a block the author wrote.
     *
     * <p>Told by the rule, which is minted where the syntax is read and carried by every copy of it.
     * A position is not that: a copy of a body a reader cannot open is stamped with the call site.
     */
    record WrittenBlock(RuleOrigin rule) implements MaterialisationSite {

        public WrittenBlock {
            if (rule == null || !rule.isWritten()) {
                throw new IllegalArgumentException("a block the source wrote: " + rule);
            }
        }
    }

    /**
     * The body of a block a pass wrote out of a name standing where a value goes.
     *
     * <p>The author wrote a name and not a block, so what settles which block this is is the
     * reference that made it necessary — a thing that was there before anything was expanded, and
     * the same one {@link ExpansionSite.Named} names a copy made at such a name by.
     *
     * <p>Told by the reference and not by what it reaches: two occurrences of one name are two
     * references and two blocks. A binding the block was read out of is not here, being this
     * compiler's own and not a thing the source settled.
     */
    record GeneratedBlock(SourceReferenceOrigin reference) implements MaterialisationSite {

        public GeneratedBlock {
            if (reference == null) {
                throw new IllegalArgumentException(
                        "a block a name was expanded into was expanded from some name a source"
                                + " wrote");
            }
        }
    }
}
