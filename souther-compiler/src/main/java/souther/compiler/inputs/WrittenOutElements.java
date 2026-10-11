package souther.compiler.inputs;

import souther.compiler.check.DeclarationNewtypes;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.types.BindingId;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * Every element a container holds, written out, in the order a walk of it meets them and each with
 * what it was kept by — where the container is a list written in the source, or a list an
 * operation put together of a piece of each element of one
 * ({@link ElementBindings#piecesOfEachElement}).
 *
 * <p>One walk for every reader that writes a container out. What a name an operation handed an
 * element on stands for ({@link InputReads#meaningOf}) and what a statement about some element of a
 * container is read element by element over are the same elements, and two walks over the
 * operations that built them would be two answers the first time one of them learned an operation
 * the other did not.
 *
 * <p>What each piece is, is what the operation is proved to make of an element, and nothing read
 * off its name. A map's piece is the step's answer on the element, read where the step is handed
 * it; a filter's is the element itself, kept where the step's answer on it holds; a flatMap's is
 * every element of the step's answer on it, written out by this same walk. What an occurrence was
 * kept by is carried down every level, each truth read where it was decided.
 *
 * <p>An occurrence a filter dropped is written out as well, kept where its truth holds. Whether it
 * holds is a question about the values, and the answer is a reader's: one that only states what
 * every value supports may take every occurrence, and one placing an application of a closure must
 * not.
 */
public final class WrittenOutElements {

    /**
     * How many occurrences a walk writes out, at every level it passes, before it stops.
     *
     * <p>A bound on the work and not on what a reader takes: an occurrence a filter drops and one at
     * a level a flatMap goes through are written out as much as one in the answer. Past it the
     * container is one this reading could write out and does not
     * ({@link ReadMeaning.MoreThanAreWrittenOut}). No reader of a condition takes more applications
     * of a closure than the readings it reads one condition in, so this is held above that figure
     * and leaves room for the levels on the way to it.
     */
    public static final int MOST_WALKED = 1024;

    private WrittenOutElements() {
    }

    /** What a walk of a container came to. */
    public sealed interface Walked {

        /** Every element, in order, each with what it was kept by. Empty where it holds none. */
        record Each(List<ReadMeaning.Occurrence> each) implements Walked {

            public Each {
                each = List.copyOf(each);
            }
        }

        /** More than {@link #MOST_WALKED} on the way. */
        record PastTheFigure() implements Walked {}

        /** Not a container this walk writes out. */
        record NotWrittenOut() implements Walked {}
    }

    /** Every element {@code container}, standing where it is followed to, holds. */
    public static Walked of(Denotation container, Symbols symbols, DeclarationNewtypes newtypes) {
        return of(container, symbols, newtypes, new HashSet<>());
    }

    /** The same, inside a walk that has already met the names {@code met}. */
    static Walked of(Denotation container, Symbols symbols, DeclarationNewtypes newtypes,
                     Set<BindingId> met) {
        int[] walked = {0};
        return of(container, symbols, newtypes, met, walked);
    }

    private static Walked of(Denotation container, Symbols symbols, DeclarationNewtypes newtypes,
                             Set<BindingId> met, int[] walked) {
        InputReads at = container.at();
        Core value = Core.withoutStanding(container.value());
        if (value instanceof Core.ListLit written) {
            List<ReadMeaning.Occurrence> out = new ArrayList<>();
            for (Core each : written.elements()) {
                if (++walked[0] > MOST_WALKED) {
                    return new Walked.PastTheFigure();
                }
                // Which value each member is does not turn on the type it stands as in the list.
                out.add(ReadMeaning.Occurrence.always(
                        new Denotation(Core.withoutStanding(each), at)));
            }
            return new Walked.Each(out);
        }
        ElementBindings.PiecesOfEachElement pieces = ElementBindings.piecesOfEachElement(value,
                closure -> Core.withoutStanding(InputReads.standing(new Denotation(closure, at),
                        symbols, newtypes, new HashSet<>(met)).value())
                        instanceof Core.Block block ? block : null);
        if (pieces == null || pieces.element() == null || pieces.element().binding() == null) {
            return new Walked.NotWrittenOut();
        }
        Walked from = of(InputReads.standing(new Denotation(pieces.walked(), at), symbols,
                newtypes, new HashSet<>(met)), symbols, newtypes, met, walked);
        if (!(from instanceof Walked.Each(List<ReadMeaning.Occurrence> elements))) {
            return from;
        }
        BindingId element = pieces.element().binding();
        List<ReadMeaning.Occurrence> out = new ArrayList<>();
        for (ReadMeaning.Occurrence each : elements) {
            // The step's body read on the application handing it this element.
            Denotation answered = new Denotation(pieces.step().body(),
                    at.handing(element, each.value(), newtypes));
            switch (pieces.piece()) {
                case THE_CLOSURES_ANSWER -> {
                    if (++walked[0] > MOST_WALKED) {
                        return new Walked.PastTheFigure();
                    }
                    out.add(new ReadMeaning.Occurrence(answered, each.keptWhere()));
                }
                case THE_ELEMENT_WHERE_IT_HOLDS -> {
                    if (++walked[0] > MOST_WALKED) {
                        return new Walked.PastTheFigure();
                    }
                    List<ReadMeaning.Occurrence.Kept> kept = new ArrayList<>(each.keptWhere());
                    kept.add(new ReadMeaning.Occurrence.Kept(answered, true));
                    out.add(new ReadMeaning.Occurrence(each.value(), kept));
                }
                case WHAT_THE_CLOSURE_ANSWERS -> {
                    Walked inside = of(InputReads.standing(answered, symbols, newtypes,
                            new HashSet<>(met)), symbols, newtypes, met, walked);
                    if (!(inside instanceof Walked.Each(List<ReadMeaning.Occurrence> made))) {
                        return inside;
                    }
                    made.forEach(one -> out.add(one.keptAlsoWhere(each.keptWhere())));
                }
            }
        }
        return new Walked.Each(out);
    }
}
