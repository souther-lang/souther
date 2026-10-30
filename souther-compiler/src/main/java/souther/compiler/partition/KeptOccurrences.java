package souther.compiler.partition;

import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.Requirements;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.PositionsAStatementReads;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Relation;
import souther.compiler.meaning.Spelling;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Rel;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;

/**
 * The occurrences of the elements of a container that meet a statement, which is what a list
 * made by an operation that kept some of them holds.
 *
 * <p>The statement is the one a count of the elements meeting it is of
 * ({@link CountedElements}), about an element of the container and nothing else: whether an
 * occurrence is counted turns on that occurrence alone, so the same value kept at one occurrence
 * and dropped at another is counted where it is kept.
 *
 * <p>A statement that reads nothing but positions of the input, so that which places a number of
 * the kept occurrences is read off is said in full ({@link #placesRead}). One that reads
 * something no position is — an answer, a value a body bound — is kept by nothing here
 * ({@link #of}).
 *
 * @param container  where the elements are
 * @param meeting    what an element is kept for meeting
 * @param perElement {@code meeting} put to rows, which is what an element is asked
 */
public record KeptOccurrences(DecisionSubject container, Proposition meeting,
                              AStatementAtARow perElement) {

    public KeptOccurrences {
        Objects.requireNonNull(container, "kept among the elements of a container");
        Objects.requireNonNull(meeting, "by a statement about an element");
        Objects.requireNonNull(perElement, "put to rows as an element is");
        if (PositionsAStatementReads.of(meeting).isEmpty()) {
            throw new IllegalArgumentException("what keeps the elements of " + container
                    + " reads something no position is: " + meeting.spelling());
        }
    }

    /** The occurrences of {@code container}'s elements meeting {@code meeting}, or null where it
     *  reads something no position of the input is. */
    static KeptOccurrences of(DecisionSubject container, Proposition meeting,
                              AStatementAtARow perElement) {
        return PositionsAStatementReads.of(meeting).isEmpty() ? null
                : new KeptOccurrences(container, meeting, perElement);
    }

    /** The container the elements are of. */
    TermPath position() {
        return container.inputPosition();
    }

    /**
     * What an element meeting the statement is held to, as relations a region is narrowed by —
     * or empty where the statement is anything else: every element written inside a region
     * narrowed so meets it, and is kept.
     *
     * <p>A relation over the element's numbers holding or failing, and every one of several
     * holding. A relation that fails is its denial, and one that leaves a hole in an order is the
     * hole; one a region cannot carry leaves nothing to narrow by.
     */
    Optional<List<TakenConstraint>> heldTo() {
        List<TakenConstraint> out = new ArrayList<>();
        return heldTo(meeting, out) ? Optional.of(List.copyOf(out)) : Optional.empty();
    }

    private static boolean heldTo(Proposition stated, List<TakenConstraint> out) {
        return switch (stated) {
            case Proposition.All all -> all.parts().stream().allMatch(part -> heldTo(part, out));
            case Proposition.Compared(Relation.Affine affine, boolean holds, Spelling _) -> {
                LinearForm<NumericTerm> form = WhatTheDeclarationsLeave.ofTheInput(affine.form());
                Rel rel = holds ? affine.proposition() : affine.proposition().denied();
                if (form == null) {
                    yield false;
                }
                if (rel != Rel.NE) {
                    out.add(new TakenConstraint.Affine(form, rel));
                    yield true;
                }
                // A hole is in the order of one number, where it is that number less a constant.
                if (form.coefs().size() != 1
                        || !(form.coefs().entrySet().iterator().next() instanceof Map.Entry<
                                NumericTerm, ExactRatio> only)
                        || !ExactRatio.ONE.equals(only.getValue())
                        || !(only.getKey() instanceof NumericTerm.FromOnePosition term)
                        || !(Count.written(form.constant().negated())
                                instanceof ExactAnswer.Held<Optional<Count>>(
                                        Optional<Count> at))
                        || at.isEmpty()) {
                    yield false;
                }
                out.add(new TakenConstraint.AwayFrom(term, at.get()));
                yield true;
            }
            case Proposition.Compared(Relation.Ordered(DecisionAtom.OfTheInput(NumericTerm term),
                    Place at, Rel rel), boolean holds, Spelling _)
                    when term.atOnePosition() != null -> {
                Rel held = holds ? rel : rel.denied();
                out.add(TakenConstraint.Ordered.isABound(held)
                        ? new TakenConstraint.Ordered(term.atOnePosition(), at, held)
                        : new TakenConstraint.AwayFrom(term.atOnePosition(), at));
                yield true;
            }
            default -> false;
        };
    }

    /** The most distinct ways of meeting a statement that is only cases this keeps apart. */
    private static final int MOST_WAYS = 64;

    /**
     * Every way an element meets the statement, where it says no more than which cases positions
     * of the element are in — or empty where it says anything else, or has more ways than are
     * kept apart. A statement no case meets is read, and has no way.
     *
     * <p>A way is one case at each position it names, with the cases the way to that position
     * narrows to ({@link TermPath#requirements}), which is what a row is written in: a plan writes
     * one case of a sum. Ways are counted once however many statements give them. Meeting any of
     * several statements is a way of any of them, and meeting all of them a way that stands beside
     * a way of each; a pair of ways asking two cases of one position is no way. Which of the ways
     * a row is written in depends on what else the row asks of the same positions, so none is
     * chosen here.
     */
    Optional<CasesAsked> casesAsked() {
        return casesAsked(meeting);
    }

    /**
     * @param ways      each a case at every position the statement names, any one of which meets
     *                  it; none where no case does, which is a statement read and met by nothing
     * @param positions where the statement reads a case, each once
     */
    record CasesAsked(List<Requirements> ways, List<TermPath> positions) {

        CasesAsked {
            ways = List.copyOf(ways);
            positions = List.copyOf(positions);
        }
    }

    private static Optional<CasesAsked> casesAsked(Proposition stated) {
        return switch (stated) {
            case Proposition.InCases(DecisionSubject.AnInput(TermPath at), CasesLeft cases,
                    boolean holds, Spelling _) when holds -> {
                // The position exists only in the cases the way to it narrows to, so each way
                // is those cases and the case asked beside them.
                Set<Requirements> ways = new LinkedHashSet<>();
                for (Refinement atom : cases.atoms()) {
                    if (at.requirements().merge(Requirements.NONE.and(at.position(),
                            CasesLeft.of(atom))) instanceof Requirements.Merge.Merged(
                            Requirements way)) {
                        ways.add(way);
                    }
                }
                yield ways.size() > MOST_WAYS ? Optional.empty()
                        : Optional.of(new CasesAsked(List.copyOf(ways), List.of(at.position())));
            }
            case Proposition.Any any -> {
                Set<Requirements> ways = new LinkedHashSet<>();
                Set<TermPath> positions = new LinkedHashSet<>();
                for (Proposition part : any.parts()) {
                    CasesAsked here = casesAsked(part).orElse(null);
                    if (here == null) {
                        yield Optional.empty();
                    }
                    ways.addAll(here.ways());
                    positions.addAll(here.positions());
                }
                yield ways.size() > MOST_WAYS ? Optional.empty()
                        : Optional.of(new CasesAsked(List.copyOf(ways), List.copyOf(positions)));
            }
            case Proposition.All all -> {
                Set<Requirements> ways = new LinkedHashSet<>(List.of(Requirements.NONE));
                Set<TermPath> positions = new LinkedHashSet<>();
                for (Proposition part : all.parts()) {
                    CasesAsked here = casesAsked(part).orElse(null);
                    if (here == null) {
                        yield Optional.empty();
                    }
                    Set<Requirements> together = new LinkedHashSet<>();
                    for (Requirements one : ways) {
                        for (Requirements other : here.ways()) {
                            if (one.merge(other) instanceof Requirements.Merge.Merged(
                                    Requirements both)) {
                                together.add(both);
                            }
                        }
                    }
                    if (together.size() > MOST_WAYS) {
                        yield Optional.empty();
                    }
                    ways = together;
                    positions.addAll(here.positions());
                }
                yield Optional.of(new CasesAsked(List.copyOf(ways), List.copyOf(positions)));
            }
            default -> Optional.empty();
        };
    }

    /** Every place of the input this reads: where the elements are, and each position the
     *  statement reads. */
    public List<TermPath> placesRead() {
        List<TermPath> out = new ArrayList<>();
        out.add(position());
        PositionsAStatementReads.of(meeting).orElseThrow().forEach(out::add);
        return List.copyOf(out);
    }

    /** What this selects, spelled for a coordinate: the position with its narrowings, as a report
     *  spells a position, and the statement by its own spelling, which is what holds two
     *  statements apart — held as that spelling and not written out. */
    public Spelling spelling() {
        return Spelling.of(container.inputPosition().discriminated() + " meeting ",
                meeting.spelling());
    }

    /** {@link #spelling} written out, for a reader. */
    public String key() {
        return spelling().toString();
    }

    /** Two of these are one where they keep the elements of the same container by the same
     *  statement; how the statement is put to rows is the statement's own. */
    @Override
    public boolean equals(Object other) {
        return other instanceof KeptOccurrences that && container.equals(that.container)
                && meeting.equals(that.meeting);
    }

    @Override
    public int hashCode() {
        return Objects.hash(container, meeting);
    }
}
