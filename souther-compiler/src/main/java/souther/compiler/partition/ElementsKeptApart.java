package souther.compiler.partition;

import souther.compiler.check.ElementsApart;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.Shape;
import souther.compiler.check.TypeView;
import souther.compiler.revision.RevisionKnowledge;
import souther.compiler.revision.RevisionWork;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

/**
 * What a list or a set built here keeps its elements apart at, as {@link ElementsApart} answers it,
 * with each name's rules read once for the revision.
 *
 * <p>A container is built at every point and every settling a search visits, and what a name's
 * rules keep apart is about the name and nothing about where the search is — so the reading of
 * them is work the revision keeps ({@link WrittenOn}) and not a reading made again per container.
 */
final class ElementsKeptApart {

    /** What the elements of {@code view} are to be apart at, and nothing where they may repeat. */
    static List<List<String>> at(TypeView view, RuleReadingContext reading) {
        return at(view.wrappers(), view.shape(), reading);
    }

    /** The same, of a position read as the names it wears and the shape under them. */
    static List<List<String>> at(List<TypeSymbol> worn, Shape shape, RuleReadingContext reading) {
        if (!(shape instanceof Shape.Sequence)) {
            return List.of();
        }
        List<List<String>> written = new ArrayList<>();
        for (TypeSymbol each : worn) {
            if (each instanceof TypeSymbol.AtModule named) {
                written.addAll(reading.revision().settled(new WrittenOn(named, reading.source())));
            }
        }
        return ElementsApart.of(shape, written);
    }

    /**
     * What the rules written on one name keep the elements of its value apart at, as work settled
     * by the name and the source its rules are read from.
     *
     * <p>The source by its origin, as a record composed for the revision is keyed
     * ({@link Partitions.ARecordComposed}): two sources with one origin are one world to read in,
     * and the source carried is what does the work and no part of which work this is.
     */
    static final class WrittenOn implements RevisionWork<List<List<String>>> {

        private final TypeSymbol.AtModule named;

        private final RuleReadingSource.Origin origin;

        private final RuleReadingSource source;

        WrittenOn(TypeSymbol.AtModule named, RuleReadingSource source) {
            this.named = named;
            this.origin = source.origin();
            this.source = source;
        }

        @Override
        public List<List<String>> workedOut(RevisionKnowledge revision) {
            return ElementsApart.writtenOn(named, source);
        }

        @Override
        public boolean equals(Object other) {
            return other instanceof WrittenOn it && named.equals(it.named)
                    && origin.equals(it.origin);
        }

        @Override
        public int hashCode() {
            return Objects.hash(named, origin);
        }

        @Override
        public String toString() {
            return "WrittenOn[" + named + "]";
        }
    }

    private ElementsKeptApart() {}
}
