package souther.compiler.report;

import souther.compiler.query.PartitionEvidence;

/**
 * Whether a report has a section to write about what a behavior's rules divide and bound.
 *
 * <p>One decision, made here, read by every surface. It used to be made twice and differently: the
 * text left the two lines out where the lists beside the measures were all empty, and the document
 * left the object out where the boundary the positions come off was not worked out. So one
 * compilation answered a reader two ways — a {@code >->} composition, which has no positions of its
 * own, wrote a {@code partition} object saying {@code no_subject} and no line of text at all; and a
 * behavior whose every rule is a bound on a {@code Decimal} wrote a document saying its rules draw
 * no line and a page saying nothing (issue #1079).
 *
 * <p><b>What a surface may do and what it may not.</b> A surface may leave a semantic result out —
 * a page for a person and a document for a program are owed different amounts of the same reading.
 * What it may not do is work out for itself whether the result exists, because that is a fact about
 * the measurement and the surfaces then disagree about the model rather than about how much to say.
 *
 * <p><b>And what is decided here is whether the section is written, not whether the measurement
 * exists.</b> One of the two absences below is a measurement nobody made; the other is a measure
 * that was asked for, started and could not be finished, and what is left of it is said as the
 * behavior's own weakening rather than as a section with no number in it. Read as one sentence
 * about the model, the second would have this deciding what a measurement is — which is the thing
 * the split is against, pointed the other way.
 */
sealed interface PartitionSection {

    /** There is a section, and this is the reading it is written from. */
    record Present(PartitionEvidence evidence) implements PartitionSection {}

    /**
     * There is none.
     *
     * <p>Carrying no reason, because nothing reads one. Two things settle it and they are two
     * different absences — see {@link #of} — and what a surface does about either is the same
     * thing: there is no measurement for a section to be about. The day one of them is worth
     * saying out loud, the reason comes back with the reader that says it.
     */
    record Omitted() implements PartitionSection {}

    /**
     * Which of the two {@code evidence} comes to.
     *
     * <p>Asked of the measurement and of nothing else. Asked of the entries beside it, a behavior
     * whose measures both had something to say and whose lists happened to be empty was written out
     * of the report — which is how a model bounded only on a {@code Decimal} came back adequate with
     * no measure printed anywhere.
     *
     * <p>Two absences here and they are not the same absence. A null is the compile not having got
     * far enough to be asked, which is not a measure that came back with nothing — every measure
     * that ran says why it has no number. A boundary that could not be worked out is the other way
     * about: the measures exist and both failed, and what this section owes is the positions, the
     * lines and the size of the space they make — every one of those a product over positions
     * nobody could count, so there is no number here to qualify. That is a policy about the
     * section and not a claim about the model, and what weakened the behavior is said once, as the
     * behavior's own weakening. It is the same reason the signature section is left out where its
     * cases could not be counted.
     */
    static PartitionSection of(PartitionEvidence evidence) {
        if (evidence == null || evidence.boundaryNotDerived()) {
            return new Omitted();
        }
        return new Present(evidence);
    }
}
