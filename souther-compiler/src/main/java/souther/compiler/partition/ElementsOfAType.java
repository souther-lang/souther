package souther.compiler.partition;

import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.Shape;
import souther.compiler.check.TypeView;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Supplier;

/**
 * The values a list may be grown by at a position of one element type when no row ran that type,
 * made as far as a search asks for them and no further.
 *
 * <p>First what the compiler stands for the type with, and what it stands for a collection of one
 * element of it where the type is a collection ({@link #withOneElement}); then, from each of those,
 * the numbers a unit away and the value with an element in a list it holds that held nothing
 * ({@link NearbyValues#populated}). The last is the same question asked of the values already made,
 * so each value that fills a list leads to the next, one level deeper in the lists and no longer
 * in any of them: a value is made when the one before it has been asked for, and the search that
 * stops asking leaves the deeper ones unmade. A type whose lists are all filled has nothing left
 * to fill, so the values of a type that does not hold itself come to an end, and the search that
 * has been given all of them has been given all there are. Every value is built by the type's own
 * decoder ({@link Generator.CandidateCheck#builtAlone}), so a type the decoder does not build on
 * its own (an optional, a tuple) or a check with no runtime offers nothing.
 *
 * <p>The values beyond the representatives are for the ones that are the identity of the body's
 * arithmetic. A sum is the same at no element as at a zero, and a count of what the elements hold
 * is the same at an empty list as at none: a collection with an element in it, and a number a unit
 * away, are the values that tell the body from a constant.
 *
 * <p>These are proposals and not observations, so they are kept apart from
 * {@link InputsRowsRanWith}: whether one of them answers, and answers differently, is what running
 * the candidate says.
 *
 * <p>Bounded, and said to be: no more than {@code most} values are made for a type, and reaching
 * that is told to {@link Stops} as the bound it is, since what was not made is not found absent.
 * What the compiler met in building the proposals the values come from is told to it as it is met.
 * A type that holds itself is read for what has been made of it so far while it is being made, so
 * it goes one level deeper each time it is asked for and is never walked to the bottom.
 */
final class ElementsOfAType {

    /** Where what stopped the making of the values is said. */
    interface Stops {

        /** The building of a proposal met {@code shortfall}. */
        void met(CompositionShortfall shortfall);

        /** The values of a type were not all made, because {@code most} of them were. */
        void limitedAt(int most);
    }

    private final Function<Type, Proposals> representatives;
    private final Function<Type, Proposals> withOneElement;
    private final RuleReadingContext reading;
    private final Generator.CandidateCheck check;
    private final int most;
    private final Stops stops;
    private final Map<Type, Values> byType = new HashMap<>();

    /**
     * @param representatives what stands for a type, with what the building of it met
     * @param withOneElement  what stands for a collection of one element of a type, which is
     *                        nothing for a type that is not a collection
     * @param reading         how the rules of the types are read
     * @param check           what builds a value of a type from a fixture
     * @param most            how many values are made for one type
     * @param stops           where what stopped the making is said
     */
    ElementsOfAType(Function<Type, Proposals> representatives,
                    Function<Type, Proposals> withOneElement, RuleReadingContext reading,
                    Generator.CandidateCheck check, int most, Stops stops) {
        this.representatives = representatives;
        this.withOneElement = withOneElement;
        this.reading = reading;
        this.check = check;
        this.most = most;
        this.stops = stops;
    }

    /**
     * What stands for a collection of one element of {@code type}, under the names the position
     * wears; nothing where it is not a collection, or wears a name this module cannot write.
     *
     * <p>The names go back on as they do on every other value that stands for a position
     * ({@link RepresentativeSource#under}): what is built here is the value inside them.
     */
    static Proposals withOneElement(Type type, RuleReadingContext reading) {
        RuleReadingSource source = reading.source();
        TypeView view = TypeView.of(type, source.inners(), source.symbols(), source.kinds(),
                source.sums());
        if (!(view.shape() instanceof Shape.Sequence)
                || !(WornNames.of(view.wrappers(), source) instanceof WornNames.Spelled spelled)) {
            return Proposals.NONE;
        }
        return Witnesses.ofSize(view, 1, List.of(), reading, Set.of())
                .map(bare -> RepresentativeSource.under(spelled.names(), bare));
    }

    /** The values a list of {@code element} may be grown by, in the order they are made. Each call
     *  reads from the first; what has been made is made once for the type. */
    Iterator<ObservedValue> of(Type element) {
        return byType.computeIfAbsent(element, Values::new).iterator();
    }

    /** What is made of one type so far, and the means of making more. */
    private final class Values {

        private final List<ObservedValue> made = new ArrayList<>();
        private final Source source;
        private boolean making;
        private boolean finished;

        Values(Type element) {
            this.source = new Source(element);
        }

        Iterator<ObservedValue> iterator() {
            return new Iterator<>() {

                private int at;

                @Override
                public boolean hasNext() {
                    return at < made.size() || makeOne();
                }

                @Override
                public ObservedValue next() {
                    if (!hasNext()) {
                        throw new NoSuchElementException();
                    }
                    return made.get(at++);
                }
            };
        }

        /** Whether one more was made. Asked again while it is being made, it is not: the type is
         *  read for what is there. */
        private boolean makeOne() {
            if (making || finished) {
                return false;
            }
            making = true;
            try {
                if (!source.hasNext()) {
                    finished = true;
                    return false;
                }
                // The bound is reached by there being one more it does not let be made, and not
                // by the last that it does: the one more is asked for and not handed over.
                if (made.size() >= most) {
                    finished = true;
                    stops.limitedAt(most);
                    return false;
                }
                made.add(source.next());
                return true;
            } finally {
                making = false;
            }
        }
    }

    /** How a value was made, which is what is made from it next. */
    private enum Origin {
        /** What stands for the type, or for a collection of one of it. */
        STOOD,
        /** A number a unit from another value. */
        UNIT,
        /** Another value with one more element in a list. */
        GROWN
    }

    /** The values of one type in the order they are made, none twice. */
    private final class Source implements Iterator<ObservedValue> {

        private record Stage(Supplier<Iterator<ObservedValue>> make, Origin origin) {}

        private final Type element;
        private final Deque<Stage> stages = new ArrayDeque<>();
        private final Set<ObservedValue> seen = new HashSet<>();
        private Iterator<ObservedValue> current = Collections.emptyIterator();
        private Origin origin = Origin.STOOD;
        private ObservedValue upcoming;

        Source(Type element) {
            this.element = element;
            stages.add(new Stage(() -> built(representatives), Origin.STOOD));
            stages.add(new Stage(() -> built(withOneElement), Origin.STOOD));
        }

        @Override
        public boolean hasNext() {
            while (upcoming == null) {
                if (current.hasNext()) {
                    ObservedValue value = current.next();
                    if (seen.add(value)) {
                        upcoming = value;
                        // A unit from a value that is itself a unit from one is the same
                        // question asked further along; a list grown from a value is a value to
                        // ask both of again.
                        if (origin != Origin.UNIT) {
                            stages.add(new Stage(() -> NearbyValues.oneUnitFrom(value, element,
                                    reading), Origin.UNIT));
                            stages.add(new Stage(() -> NearbyValues.populated(value, element,
                                    reading, ElementsOfAType.this::of), Origin.GROWN));
                        }
                    }
                } else if (!stages.isEmpty()) {
                    Stage next = stages.poll();
                    current = next.make().get();
                    origin = next.origin();
                } else {
                    return false;
                }
            }
            return true;
        }

        @Override
        public ObservedValue next() {
            if (!hasNext()) {
                throw new NoSuchElementException();
            }
            ObservedValue out = upcoming;
            upcoming = null;
            return out;
        }

        /** What the type's decoder builds of the fixtures {@code from} proposes, the compiler's
         *  stops said when the proposals are asked for. */
        private Iterator<ObservedValue> built(Function<Type, Proposals> from) {
            Proposals proposed = from.apply(element);
            stops.met(proposed.met());
            Iterator<FixtureTemplate> fixtures = proposed.values().iterator();
            return new Iterator<>() {

                private ObservedValue upcomingBuilt;

                @Override
                public boolean hasNext() {
                    while (upcomingBuilt == null && fixtures.hasNext()) {
                        upcomingBuilt = check.builtAlone(element, fixtures.next()).orElse(null);
                    }
                    return upcomingBuilt != null;
                }

                @Override
                public ObservedValue next() {
                    if (!hasNext()) {
                        throw new NoSuchElementException();
                    }
                    ObservedValue out = upcomingBuilt;
                    upcomingBuilt = null;
                    return out;
                }
            };
        }
    }
}
