package souther.compiler.partition;

import souther.compiler.check.ElementsApart;
import souther.compiler.check.FieldDomains;
import souther.compiler.check.RuleKey;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.Shape;
import souther.compiler.check.TypeView;
import souther.compiler.core.Core;
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

    /**
     * Whether two elements of {@code list} may come to one key {@code key} makes.
     *
     * <p>Not where the rules of the value the list is read off, or of the names it wears, keep its
     * elements apart at the fields the key reads: the answer the builders of the list are told
     * ({@link #at}), asked of the list as the key sees it. A key that does more than read fields off
     * an element is one nothing here follows, and its keys may repeat.
     */
    static boolean keysMayRepeat(Core list, Core.Block key, RuleReadingContext reading) {
        RuleReadingSource source = reading.source();
        List<String> run = ElementsApart.runTaken(key, source.newtypes());
        if (run == null) {
            return true;
        }
        ElementsApart.ReadOff off = ElementsApart.readOff(list, source.newtypes());
        List<List<String>> held = heldUnder(off.holder().type(), off.path(), reading);
        TypeView view = TypeView.of(list.type(), source.inners(), source.symbols(),
                source.kinds(), source.sums());
        return !ElementsApart.covers(at(view, held, reading), run);
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
     * <p>Read where that reading reads them — on the name the parameter is written under where it
     * wraps the record its fields come off, on the record otherwise ({@link Partitions#rulesOver},
     * {@link FieldDomains.Held#keptApart}) — so a value built from the path and one built from the
     * reading are kept apart at the same runs.
     *
     * <p>Kept for the revision ({@link HeldUnder}). A plan asks it of every position it builds,
     * at every point a search visits, and the answer is about the type and the path alone.
     *
     * @param path where the value is under the parameter, as its rules name it; null where they
     *             cannot name it, which is a value they say nothing of
     */
    static List<List<String>> heldUnder(Type root, RuleKey path, RuleReadingContext reading) {
        if (path == null || path.isTheValueItself()) {
            return List.of();
        }
        return reading.revision().settled(new HeldUnder(root, path, reading.source()));
    }

    /**
     * What the rules over the value at a path under a parameter's type keep its elements apart at,
     * as work settled by the type, the path and the source its rules are read from — by its origin,
     * as {@link WrittenOn} is.
     */
    static final class HeldUnder implements RevisionWork<List<List<String>>> {

        private final Type root;

        private final RuleKey path;

        private final RuleReadingSource.Origin origin;

        private final RuleReadingSource source;

        HeldUnder(Type root, RuleKey path, RuleReadingSource source) {
            this.root = root;
            this.path = path;
            this.origin = source.origin();
            this.source = source;
        }

        @Override
        public List<List<String>> workedOut(RevisionKnowledge revision) {
            if (!(TypeView.shapeOf(root, source.inners(), source.symbols(), source.kinds(),
                    source.sums())
                    instanceof Shape.Product(TypeSymbol.AtModule declared, var _))) {
                return List.of();
            }
            return ElementsApart.heldAt(new Type.Ref(Partitions.rulesOver(root, declared, source)),
                    path, named -> revision.settled(new WrittenOn(named, source)), source);
        }

        @Override
        public boolean equals(Object other) {
            return other instanceof HeldUnder it && root.equals(it.root) && path.equals(it.path)
                    && origin.equals(it.origin);
        }

        @Override
        public int hashCode() {
            return Objects.hash(root, path, origin);
        }

        @Override
        public String toString() {
            return "HeldUnder[" + root + " at " + path + "]";
        }
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
