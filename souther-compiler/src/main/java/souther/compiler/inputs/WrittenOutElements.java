package souther.compiler.inputs;

import souther.compiler.check.Choice;
import souther.compiler.check.DeclarationNewtypes;
import souther.compiler.check.ElementsWrittenOut;
import souther.compiler.check.LawAtACall;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.types.BindingId;

import java.util.HashSet;
import java.util.List;
import java.util.Objects;
import java.util.Optional;
import java.util.OptionalLong;
import java.util.Set;

/**
 * Every element a container holds, written out ({@link ElementsWrittenOut}), each read in this
 * reading of names.
 *
 * <p>The walk is {@link ElementsWrittenOut}'s, which the discharge of a rule walks as well; this
 * hands it how names are followed here and how an application of a step hands its parameter an
 * element ({@link InputReads#handing}), and takes what it wrote out as {@link ReadMeaning}'s
 * occurrences. What a name an operation handed an element on stands for
 * ({@link InputReads#meaningOf}) and what a statement about some element of a container is read
 * element by element over are the same elements.
 *
 * <p>An occurrence a filter dropped is written out as well, kept where its truth holds. Whether it
 * holds is a question about the values, and the answer is a reader's: one that only states what
 * every value supports may take every occurrence, and one placing an application of a closure must
 * not.
 */
public final class WrittenOutElements {

    private WrittenOutElements() {
    }

    /** What a walk of a container came to. */
    public sealed interface Walked {

        /**
         * Every element, in order, each with what it was kept by — none where it holds none. A
         * reader outside this reading of names takes them as {@link ReadMeaning.OneOf} hands them
         * out: through what decides which of them are there.
         */
        final class Each implements Walked {

            private final List<ReadMeaning.Occurrence> each;

            Each(List<ReadMeaning.Occurrence> each) {
                this.each = List.copyOf(each);
            }

            /** The occurrences there on some row ({@link ReadMeaning.OneOf#occurrencesWhere}). */
            public List<ReadMeaning.Occurrence> occurrencesWhere(ReadMeaning.WhereKept kept) {
                return ReadMeaning.decided(each, kept);
            }

            /** Every occurrence as written. */
            List<ReadMeaning.Occurrence> asWritten() {
                return each;
            }
        }

        /** More than {@link ElementsWrittenOut#MOST_WALKED} on the way. */
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
        return switch (ElementsWrittenOut.of(new ElementsWrittenOut.Stood<>(container.value(),
                container.at()), new Names(symbols, newtypes, met))) {
            case ElementsWrittenOut.Walked.Each<InputReads>(var each) ->
                    new Walked.Each(each.stream().map(WrittenOutElements::occurrence).toList());
            case ElementsWrittenOut.Walked.PastTheFigure<InputReads> _ ->
                    new Walked.PastTheFigure();
            case ElementsWrittenOut.Walked.NotWrittenOut<InputReads> _ ->
                    new Walked.NotWrittenOut();
        };
    }

    /** How many elements {@code container}, standing where it is followed to, holds where it is
     *  written out with each of them there on every run ({@link ElementsWrittenOut#sizeOf}). */
    public static OptionalLong sizeOf(Denotation container, Symbols symbols,
                                      DeclarationNewtypes newtypes) {
        return ElementsWrittenOut.sizeOf(new ElementsWrittenOut.Stood<>(container.value(),
                container.at()), new Names(symbols, newtypes, Set.of()));
    }

    /** How a walk of the elements of a container reads names here, for a reading that walks them
     *  itself ({@link LawAtACall}). */
    public static ElementsWrittenOut.Reading<InputReads> reading(Symbols symbols,
                                                                 DeclarationNewtypes newtypes) {
        return new Names(symbols, newtypes, Set.of());
    }

    private static ReadMeaning.Occurrence occurrence(ElementsWrittenOut.Occurrence<InputReads> one) {
        return new ReadMeaning.Occurrence(denotation(one.value()), one.keptWhere().stream()
                .map(WrittenOutElements::kept).toList());
    }

    private static ReadMeaning.Occurrence.Kept kept(ElementsWrittenOut.Kept<InputReads> kept) {
        return switch (kept) {
            case ElementsWrittenOut.Kept.ATruth<InputReads>(var truth, boolean holds) ->
                    new ReadMeaning.Occurrence.Kept.ATruth(denotation(truth), holds);
            case ElementsWrittenOut.Kept.AnArm<InputReads>(var fork, int part) ->
                    new ReadMeaning.Occurrence.Kept.AnArm(denotation(fork), part);
        };
    }

    private static Denotation denotation(ElementsWrittenOut.Stood<InputReads> stood) {
        return new Denotation(stood.value(), stood.at());
    }

    /**
     * How the walk reads names here: followed by this reading ({@link InputReads#standing}), stopping
     * at the names {@code met} already, and handed to a step's parameter as an application hands one.
     */
    private record Names(Symbols symbols, DeclarationNewtypes newtypes, Set<BindingId> met)
            implements ElementsWrittenOut.Reading<InputReads> {

        Names {
            Objects.requireNonNull(symbols, "names are followed against some library");
            Objects.requireNonNull(newtypes, "and some declarations' newtypes");
            Objects.requireNonNull(met, "having met some names, or none");
        }

        @Override
        public ElementsWrittenOut.Stood<InputReads> standing(Core e, InputReads at) {
            Denotation stood = InputReads.standing(new Denotation(e, at), symbols, newtypes,
                    new HashSet<>(met));
            return new ElementsWrittenOut.Stood<>(stood.value(), stood.at());
        }

        @Override
        public InputReads handing(InputReads at, BindingId element,
                                  ElementsWrittenOut.Stood<InputReads> value) {
            return at.handing(element, denotation(value), newtypes);
        }

        @Override
        public InputReads choosing(InputReads at, Choice.Decides decidedBy) {
            return at.choosing(decidedBy, symbols, newtypes);
        }

        @Override
        public Optional<Object> folded(ElementsWrittenOut.Stood<InputReads> value) {
            return value.at().folded(value.value(), symbols, newtypes);
        }
    }
}
