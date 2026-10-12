package souther.compiler.partition;

import souther.compiler.check.ElementsApart;
import souther.compiler.check.FieldDomains;
import souther.compiler.check.RuleKey;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.Shape;
import souther.compiler.check.TypeView;
import souther.compiler.revision.RevisionKnowledge;
import souther.compiler.revision.RevisionWork;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
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

    /**
     * What the elements of {@code view} are to be apart at, and nothing where they may repeat.
     *
     * @param held what the rules of the value holding this one keep its elements apart at
     *             ({@link FieldDomains.Held#keptApart}), nothing where nothing holds it or they say
     *             nothing of it
     */
    static List<List<String>> at(TypeView view, List<List<String>> held,
                                 RuleReadingContext reading) {
        return at(view.wrappers(), view.shape(), held, reading);
    }

    /** The same, of a position read as the names it wears and the shape under them. */
    static List<List<String>> at(List<TypeSymbol> worn, Shape shape, List<List<String>> held,
                                 RuleReadingContext reading) {
        if (!(shape instanceof Shape.Sequence)) {
            return List.of();
        }
        List<List<String>> written = new ArrayList<>(held);
        for (TypeSymbol each : worn) {
            if (each instanceof TypeSymbol.AtModule named) {
                written.addAll(reading.revision().settled(new WrittenOn(named, reading.source()))
                        .getOrDefault(RuleKey.THE_VALUE, List.of()));
            }
        }
        return ElementsApart.of(shape, written);
    }

    /** What the rules of a value holding another keep that one's elements apart at, as
     *  {@code held} carries it: nothing where nothing holds it. */
    static List<List<String>> heldBy(FieldDomains.Held held) {
        return held == null ? List.of() : held.keptApart();
    }

    /**
     * The same, of the value at {@code path} under a parameter of type {@code root}, for a caller
     * holding the path and not a reading of the parameter's rules.
     *
     * <p>Read where that reading reads them — on the record the parameter's fields come off
     * ({@link FieldDomains.Held#keptApart}) — so a value built from the path and one built from the
     * reading are kept apart at the same runs.
     *
     * @param path where the value is under the parameter, as its rules name it; null where they
     *             cannot name it, which is a value they say nothing of
     */
    static List<List<String>> heldUnder(Type root, RuleKey path, RuleReadingContext reading) {
        RuleReadingSource source = reading.source();
        if (path == null || path.isTheValueItself()
                || !(TypeView.shapeOf(root, source.inners(), source.symbols(), source.kinds(),
                        source.sums())
                        instanceof Shape.Product(TypeSymbol.AtModule declared, var _))) {
            return List.of();
        }
        return ElementsApart.heldAt(new Type.Ref(declared), path,
                named -> reading.revision().settled(new WrittenOn(named, source)), source);
    }

    /**
     * What the rules written on one name keep the elements of its value apart at, as work settled
     * by the name and the source its rules are read from.
     *
     * <p>The source by its origin, as a record composed for the revision is keyed
     * ({@link Partitions.ARecordComposed}): two sources with one origin are one world to read in,
     * and the source carried is what does the work and no part of which work this is.
     */
    static final class WrittenOn implements RevisionWork<Map<RuleKey, List<List<String>>>> {

        private final TypeSymbol.AtModule named;

        private final RuleReadingSource.Origin origin;

        private final RuleReadingSource source;

        WrittenOn(TypeSymbol.AtModule named, RuleReadingSource source) {
            this.named = named;
            this.origin = source.origin();
            this.source = source;
        }

        @Override
        public Map<RuleKey, List<List<String>>> workedOut(RevisionKnowledge revision) {
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
