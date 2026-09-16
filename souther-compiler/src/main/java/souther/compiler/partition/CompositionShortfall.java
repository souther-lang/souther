package souther.compiler.partition;

import java.util.Collection;
import java.util.EnumSet;
import java.util.Set;

/**
 * What of this compiler's a search that composed nothing met on the way.
 *
 * <p>A figure it holds its work to, a population it writes some of, or both. Nothing here is about
 * the model: a reader handed one of these is being told that the question is open because this
 * compiler did not go all the way, which is never what somebody wrote.
 *
 * <p><b>Which of the two is not a case.</b> What a reader concludes is the same either way, and
 * what differs is what would close it — raising a number, or somebody writing the rest of what this
 * walks. So both vocabularies are carried under their own names, and a search that met one of them
 * says so by the other being empty rather than by being a different shape.
 *
 * <p><b>Beside the word a search comes back with and never inside it.</b> The word is read off the
 * figures wherever a figure is what stopped the search ({@link
 * Generator.UnresolvedCombination.Reason#wordFor}), so a word carrying them would be one answer
 * kept twice. And what two searches met is not what tells them apart: two runs of one plan have to
 * agree on the word, and may well have met different figures on the way to it.
 *
 * <p>Made where the figure was reached or where the walk ran to the end of what this compiler
 * writes, and carried out from there. Worked out afterwards, it would be worked out from the word —
 * which is the one thing that has already lost it.
 *
 * @param figures     numbers of this compiler's that stopped it, each one somebody can raise to
 *                    have the search go on
 * @param populations what it writes some of rather than all of, which no figure reaches
 */
public record CompositionShortfall(Set<CompositionBudget> figures,
                                   Set<CompositionRepertoire> populations) {

    /** A search that met nothing of this compiler's, which is what came back about the model. */
    public static final CompositionShortfall NONE =
            new CompositionShortfall(Set.of(), Set.of());

    public CompositionShortfall {
        figures = Set.copyOf(figures);
        populations = Set.copyOf(populations);
    }

    /** One that met these figures and nothing it knows it walked part of. */
    public static CompositionShortfall of(Collection<CompositionBudget> figures) {
        return of(figures, Set.of());
    }

    /** One that met what a walk ran to the end of, and no figure. */
    public static CompositionShortfall writing(Collection<CompositionRepertoire> populations) {
        return of(Set.of(), populations);
    }

    public static CompositionShortfall of(Collection<CompositionBudget> figures,
                                          Collection<CompositionRepertoire> populations) {
        return figures.isEmpty() && populations.isEmpty()
                ? NONE : new CompositionShortfall(Set.copyOf(figures), Set.copyOf(populations));
    }

    /** Whether there is anything of this compiler's here to tell a reader about. */
    public boolean nothing() {
        return figures.isEmpty() && populations.isEmpty();
    }

    /**
     * What two searches met together.
     *
     * <p>Every one of them and not the first: two searches that fell short in two ways leave a
     * reader both pieces of work, and one dropped for the other is a number raised that changes
     * nothing. The two vocabularies are folded apart, because what closes one is not what closes
     * the other.
     */
    public CompositionShortfall and(CompositionShortfall other) {
        if (other.nothing()) {
            return this;
        }
        if (nothing()) {
            return other;
        }
        Set<CompositionBudget> both = EnumSet.noneOf(CompositionBudget.class);
        both.addAll(figures);
        both.addAll(other.figures());
        Set<CompositionRepertoire> writes = EnumSet.noneOf(CompositionRepertoire.class);
        writes.addAll(populations);
        writes.addAll(other.populations());
        return new CompositionShortfall(both, writes);
    }
}
