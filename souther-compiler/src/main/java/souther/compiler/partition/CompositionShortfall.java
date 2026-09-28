package souther.compiler.partition;

import java.util.Collection;
import java.util.EnumSet;
import java.util.HashSet;
import java.util.Set;

/**
 * What of this compiler's a search that composed nothing met on the way.
 *
 * <p>A figure it holds its work to, a population it writes some of, a number it worked out and
 * could not hold, or more than one of them. Nothing here is about the model: a reader handed one of
 * these is being told that the question is open because this compiler did not go all the way,
 * which is never what somebody wrote.
 *
 * <p><b>Which of them it was is not a case.</b> What a reader concludes is the same whichever it
 * was, and what differs is what would close it — raising a number, somebody writing the rest of
 * what this walks, a host with more room, or, for a number no representation holds, nothing. So
 * every vocabulary is carried under its own name, and a search that met some of them says so by
 * the others being empty rather than by being a different shape.
 *
 * <p><b>One value wherever it travels.</b> A carrier that took the vocabularies apart into a set
 * each would have to be taught every vocabulary there will ever be, and one it was not taught would
 * be left out without a word; joined with {@link #and}, every one of them travels together.
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
 * @param unheld      numbers it worked out and could not hold, which a host with more room
 *                    reaches where it is room that ran out, and nothing reaches where no
 *                    representation of the number exists
 */
public record CompositionShortfall(Set<CompositionBudget> figures,
                                   Set<CompositionRepertoire> populations,
                                   Set<CompositionCapacity> unheld) {

    /** A search that met nothing of this compiler's, which is what came back about the model. */
    public static final CompositionShortfall NONE =
            new CompositionShortfall(Set.of(), Set.of(), Set.of());

    public CompositionShortfall {
        figures = Set.copyOf(figures);
        populations = Set.copyOf(populations);
        unheld = Set.copyOf(unheld);
    }

    /** One that met these figures and nothing else. */
    public static CompositionShortfall of(Collection<CompositionBudget> figures) {
        return of(figures, Set.of(), Set.of());
    }

    /** One that met what a walk ran to the end of, and nothing else. */
    public static CompositionShortfall writing(Collection<CompositionRepertoire> populations) {
        return of(Set.of(), populations, Set.of());
    }

    /** Every vocabulary, named: there is no shorter spelling of this that leaves one out. */
    public static CompositionShortfall of(Collection<CompositionBudget> figures,
                                          Collection<CompositionRepertoire> populations,
                                          Collection<CompositionCapacity> unheld) {
        return figures.isEmpty() && populations.isEmpty() && unheld.isEmpty()
                ? NONE : new CompositionShortfall(Set.copyOf(figures), Set.copyOf(populations),
                        Set.copyOf(unheld));
    }

    /** Whether there is anything of this compiler's here to tell a reader about. */
    public boolean nothing() {
        return figures.isEmpty() && populations.isEmpty() && unheld.isEmpty();
    }

    /**
     * What two searches met together.
     *
     * <p>Every one of them and not the first: two searches that fell short in two ways leave a
     * reader both pieces of work, and one dropped for the other is a number raised that changes
     * nothing. The three vocabularies are folded apart, because what closes one is not what closes
     * another.
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
        Set<CompositionCapacity> notHeld = new HashSet<>(unheld);
        notHeld.addAll(other.unheld());
        return new CompositionShortfall(both, writes, notHeld);
    }
}
