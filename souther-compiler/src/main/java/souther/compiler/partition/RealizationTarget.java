package souther.compiler.partition;

import souther.compiler.inputs.NameReach;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;

/**
 * The value a row rebuilds to put a number where a search asked for it.
 *
 * <p><b>The one place where a number's reading becomes a row's writing.</b> A {@link NumericTerm}
 * says what number is meant and where it is read from, and says nothing about where a row writes:
 * the values a walk added up stood in no location at all, and the term for them names where they
 * came from precisely so that the two are not confused ({@code inputs.RunSource}). What a search
 * hands back has to be acted on, though, and acting on it is writing somewhere — so the reading is
 * turned into a write root here, once, and every reader that composes a row asks this rather than
 * working it out from the kind of term it is holding.
 *
 * <p>Which is why this is not in {@code inputs}. A write root is the generator's word for the
 * generator's problem, and a term that answered it would name this side's vocabulary from the side
 * that only measures.
 *
 * <p><b>Total, so a term of a new kind is a compilation error here.</b> Every number this compiler
 * has is realized by rebuilding one value, and which value that is is the whole of what this
 * answers. A kind of term arriving that no single value realizes does not belong in either variant,
 * and what should happen then is that this switch stops compiling and the vocabulary is looked at
 * again — not that the new term quietly joins the ones nothing composes a row for.
 *
 * <p>Whether anything can be built at a target is a different question and is not asked here.
 * {@link TermRealizations} owns it, and answers it for a target that exists — so "there is nowhere
 * to write this" and "nothing writes this" stay two sentences with one owner apiece.
 */
public sealed interface RealizationTarget {

    /** The number to be realized, which is what the rules and the report are about. */
    NumericTerm term();

    /**
     * The location whose whole value is rebuilt so that {@link #term} answers what was asked.
     *
     * <p>Not where the number is written. {@code List.sum(lines[*].amount)} is answered by no
     * location and its root is {@code lines}, at which no total is written and out of which every
     * total is made. What this promises is only that a row that rebuilds the value here can move
     * the number, and that a row that does not cannot.
     */
    TermPath writeRoot();

    /**
     * The target of a number, which every number has.
     *
     * <p>Exhaustive over the terms there are, with no {@code default} and no null. Read off a
     * condition instead, a kind of term added would fall to whichever side the last reader's
     * condition left it on, which is where "nothing composes one" was said of a number nothing had
     * been asked to compose.
     *
     * <p>Where the number is read and where it is written are one location here, because a term
     * says nothing about where a name stands. A caller that knows where the walk saw the name stand
     * builds {@link AtOnePositionUnderACase} instead — and only such a caller can, which is why
     * this answers with the place the term names rather than guessing at a case.
     */
    static RealizationTarget of(NumericTerm term) {
        return switch (term) {
            case NumericTerm.FromOnePosition one -> new AtOnePosition(one);
            case NumericTerm.TakenOver over -> new OverARun(over);
        };
    }

    /**
     * A number one position answers, realized by writing a value at that position.
     *
     * <p>The root and the position are the same location here, which is the case the vocabulary
     * grew out of and is not what a root means.
     */
    record AtOnePosition(NumericTerm.FromOnePosition term) implements RealizationTarget {

        @Override
        public TermPath writeRoot() {
            return term.position();
        }

        @Override
        public String toString() {
            return term.toString();
        }
    }

    /**
     * A number read at a name every case of a sum spreads, realized by writing the value under one
     * of those cases.
     *
     * <p><b>Where the two places come apart.</b> The number is the one the rules and the report are
     * about and it is read at the sum's own name; the value answering it is written under whichever
     * case the row turns out to be. Said as one place, the row would be asked to write at the sum's
     * name — which is a location no value goes to, and the answer for a condition over such a name
     * was that nothing here composes one.
     *
     * <p>The case is part of this and not chosen further down. A row is one value, so every name of
     * one sum is written under one case: two of these disagreeing about the case would be a row
     * asked to be both, and a reader further on has no way to tell that the pair came from one sum.
     *
     * @param term  the number, read where the rules name it
     * @param under where that number stands once the value is the case this is for, which is the
     *              location whose whole value the row rebuilds
     */
    record AtOnePositionUnderACase(NumericTerm.FromOnePosition term,
                                   NameReach.CaseStanding under) implements RealizationTarget {

        public AtOnePositionUnderACase {
            if (term == null || under == null) {
                throw new IllegalArgumentException(
                        "a number written under a case is a number, and a case it is written"
                                + " under");
            }
        }

        @Override
        public TermPath writeRoot() {
            return under.position();
        }

        @Override
        public String toString() {
            return term + " at " + under.position();
        }
    }

    /**
     * A number taken over a run of values, realized by writing the sequence they are read from.
     *
     * <p>What makes the root one location is the run's own invariant: a run is over every occurrence
     * of the path it is read from, and a path standing inside two sequences is not one
     * ({@code inputs.RunSource}). So there is exactly one sequence holding all of the values, and
     * rebuilding it is the whole of what moves the number.
     *
     * <p>The values themselves are not written anywhere and no position of the row holds them. A
     * row that fixed the place they are read from would fix one of them, which is a rule about one
     * value where the model wrote one about what they come to.
     */
    record OverARun(NumericTerm.TakenOver term) implements RealizationTarget {

        @Override
        public TermPath writeRoot() {
            return term.source().subjectPath().containingSequence();
        }

        @Override
        public String toString() {
            return term.toString();
        }
    }
}
