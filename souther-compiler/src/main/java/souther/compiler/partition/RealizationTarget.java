package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.RunSource;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.Proposition;

import java.util.List;
import java.util.Optional;

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
 *
 * <p><b>Two kinds of demand, and only one of them is a number of the row.</b> A number is read off
 * the row's values and a search can put it to the rules ({@link OfANumber}). How many elements of a
 * container meet a statement is read off every element and whatever else the statement names, and
 * is no number the rules hold a range of ({@link ACount}). Both are met by rebuilding one value, so
 * both are targets; a reader that asks for the number asks it of the first kind only.
 */
public sealed interface RealizationTarget {

    /**
     * The location whose whole value is rebuilt so that what is asked of it is answered: the
     * number a {@link OfANumber} names, or how many elements an {@link ACount} counts.
     *
     * <p>Not where the number is written. {@code List.sum(lines[*].amount)} is answered by no
     * location and its root is {@code lines}, at which no total is written and out of which every
     * total is made. What this promises is only that a row that rebuilds the value here can move
     * the number, and that a row that does not cannot.
     */
    TermPath writeRoot();

    /**
     * Where the value this target is for stands, where it is for a value an input holds that is
     * not the target's own to write — the key a count of elements, or a total of them, is asked
     * for — and null where it is not.
     *
     * <p>Another parameter's, and fixed with the rest of the row before the container is
     * composed holding it.
     */
    default TermPath keyAskedFor() {
        return null;
    }

    /**
     * Whether the value at {@link #keyAskedFor} is the number this target is asked for, so that
     * the two are chosen together and the key is not placed before the number it is.
     */
    default boolean keyIsTheNumber() {
        return false;
    }

    /**
     * Whether the key of this target is placed at another value than the key of {@code other}.
     *
     * <p>Two keys told apart by the same way from an element to its key are two keys of one
     * fold, and the row that has them apart is the one whose elements of each come to a number
     * of their own: held at one value they are one key, whose elements come to one number
     * between them.
     */
    default boolean keyIsToldApartFrom(RealizationTarget other) {
        AskedKey mine = askedKey();
        AskedKey theirs = other.askedKey();
        return mine != null && theirs != null && mine.elements().equals(theirs.elements())
                && mine.keyAt().equals(theirs.keyAt()) && !mine.asked().equals(theirs.asked());
    }

    /** The key of the elements this target is asked about, or null where it is about no such key. */
    default AskedKey askedKey() {
        return null;
    }

    /**
     * The key a target asks about ({@link #askedKey}).
     *
     * @param elements where the elements stand
     * @param keyAt    the field of an element that is its key
     * @param asked    the input whose value the key is asked for
     */
    record AskedKey(TermPath elements, TermPath keyAt, TermPath asked) {}

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
     * builds {@link AtOnePositionElsewhere} instead — and only such a caller can, which is why
     * this answers with the place the term names rather than guessing at a case.
     */
    static OfANumber of(NumericTerm term) {
        return switch (term) {
            case NumericTerm.Multiplicity among -> new AmongTheElements(among);
            case NumericTerm.ExtremeOfItsKey extreme -> new AtItsKey(extreme);
            case NumericTerm.GatheredUnderItsKey gathered -> new UnderItsKey(gathered);
            case NumericTerm.GatheredUnderAKey asked -> new UnderAKey(asked);
            case NumericTerm.OccurrencesOfItsValue among -> new AmongEveryOccurrence(among);
            case NumericTerm.OccurrencesOfAKey asked -> new AmongEveryOccurrenceEqualToAKey(asked);
            case NumericTerm.FromOnePosition one -> new AtOnePosition(one);
            case NumericTerm.TakenOver over -> new OverARun(over);
        };
    }

    /** A number of the row, which the rules hold a range of and a search can put to them. */
    sealed interface OfANumber extends RealizationTarget {

        /** The number to be realized, which is what the rules and the report are about. */
        NumericTerm term();
    }

    /**
     * A number one position answers, realized by writing a value at that position.
     *
     * <p>The root and the position are the same location here, which is the case the vocabulary
     * grew out of and is not what a root means.
     */
    record AtOnePosition(NumericTerm.FromOnePosition term) implements OfANumber {

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
     * A number read at one place and written at another, which is what a name every case of a sum
     * spreads comes to.
     *
     * <p><b>Where the two places come apart.</b> The number is the one the rules and the report are
     * about and it is read at the sum's own name; the value answering it is written under whichever
     * case the row turns out to be. Said as one place, the row would be asked to write at the sum's
     * name — which is a location no value goes to, and the answer for a condition over such a name
     * was that nothing here composes one.
     *
     * <p><b>The place and not the steps taken to reach it.</b> A name under two sums is written two
     * cases down, and how many crossings that was is the routing's business and no part of what a
     * row writes. Held as the one case taken, this type would say that a name is ever only one
     * crossing from where it is written, which is a limit of a search written into the vocabulary
     * every reader of a target shares.
     *
     * <p>What the row has to be to hold the value is read off {@link #writeRoot} and is not a second
     * component here: a path states the narrowings taken to reach it
     * ({@link TermPath#requirements}), and a case recorded beside it would be a second answer free
     * to disagree with the path it is about.
     *
     * @param term      the number, read where the rules name it
     * @param writeRoot where the value answering it stands, which is the location whose whole value
     *                  the row rebuilds
     */
    record AtOnePositionElsewhere(NumericTerm.FromOnePosition term,
                                  TermPath writeRoot) implements OfANumber {

        public AtOnePositionElsewhere {
            if (term == null || writeRoot == null) {
                throw new IllegalArgumentException(
                        "a number written away from where it is read is a number, and a place it"
                                + " is written at");
            }
            if (writeRoot.equals(term.position())) {
                throw new IllegalArgumentException(
                        "a number written where it is read is an AtOnePosition, and this one is at "
                                + writeRoot);
            }
        }

        @Override
        public String toString() {
            return term + " at " + writeRoot;
        }
    }

    /**
     * How often the value at a place occurs among every occurrence of it, realized by writing the
     * outermost container the occurrences stand in with that many of them holding the value.
     *
     * <p>A number one position reads and no position holds, as {@link AmongTheElements} is, but
     * over the containers inside the elements of another: the occurrences are spread over them, so
     * the row that moves the number is one that rebuilds the outermost container.
     */
    record AmongEveryOccurrence(NumericTerm.OccurrencesOfItsValue term) implements OfANumber {

        @Override
        public TermPath writeRoot() {
            return term.subjectPath().outermostContainer();
        }

        @Override
        public String toString() {
            return term.toString();
        }
    }

    /**
     * How often the value an input holds occurs among every occurrence of a place, realized by
     * writing the outermost container the occurrences stand in with that many of them holding it.
     *
     * <p>As {@link AmongEveryOccurrence} is, except that the value counted for is not one of those
     * at the place: it is the key's, which the row holds as another input and which is fixed with
     * the rest of the row, so a count of nought is a row where none of them holds it.
     */
    record AmongEveryOccurrenceEqualToAKey(NumericTerm.OccurrencesOfAKey term)
            implements OfANumber {

        @Override
        public TermPath writeRoot() {
            return term.subjectPath().outermostContainer();
        }

        @Override
        public TermPath keyAskedFor() {
            return term.key();
        }

        @Override
        public String toString() {
            return term.toString();
        }
    }

    /**
     * A number taken over a run of values, realized by writing the container they are read from.
     *
     * <p>What makes the root one location is the run's own invariant: a run is over every occurrence
     * of the path it is read from ({@code inputs.RunSource}). So the outermost container holds all
     * of the values, and rebuilding it is the whole of what moves the number — whether they stand
     * in the elements of it or in containers inside those.
     *
     * <p>The values themselves are not written anywhere and no position of the row holds them. A
     * row that fixed the place they are read from would fix one of them, which is a rule about one
     * value where the model wrote one about what they come to.
     */
    record OverARun(NumericTerm.TakenOver term) implements OfANumber {

        @Override
        public TermPath writeRoot() {
            // The nodes of a tree are counted by writing what is below its root, which holds the
            // root's own number nothing moves.
            if (term.source() instanceof RunSource.ReachableNodes nodes
                    && nodes.container().isEmpty()) {
                return nodes.root().then(nodes.through().getFirst());
            }
            return term.source().subjectPath().outermostContainer();
        }

        @Override
        public String toString() {
            return term.toString();
        }
    }

    /**
     * How often the value an element holds occurs among the elements of its container, realized by
     * writing the container with that many elements holding it.
     *
     * <p>A number one position reads and no position holds: it is the number of elements the
     * container has at the element's value, so the row that moves it is one that rebuilds the
     * container, as it is for a total of what the container holds.
     */
    record AmongTheElements(NumericTerm.Multiplicity term) implements OfANumber {

        @Override
        public TermPath writeRoot() {
            return term.container().element().outermostContainer();
        }

        @Override
        public String toString() {
            return term.toString();
        }
    }

    /**
     * The least or greatest of the values the elements of one key hold, realized by writing the
     * value at the place it is taken of.
     *
     * <p>An element alone under its key reads its own value, so a value written there is the
     * number wherever no other element of that key holds a value past it. Whether one does is what
     * the row holds beside it, which the candidate is read back against as a whole
     * ({@code Generator.readBack}), so a value written here and moved by a neighbour is refused
     * rather than taken for the number.
     */
    record AtItsKey(NumericTerm.ExtremeOfItsKey term) implements OfANumber {

        @Override
        public TermPath writeRoot() {
            return term.value();
        }

        @Override
        public String toString() {
            return term.toString();
        }
    }

    /**
     * What the elements of one key come to, realized by writing the container the elements stand
     * in with elements whose numbers come to it.
     *
     * <p>Written as a total over the container is ({@link ContainersAddingUp}): an end as one
     * element, which comes to its own number by either end, and a total as elements adding up to
     * it. They come to the number where they are all of one key and no other element shares it,
     * and whether they are is what the row holds beside them — read back whole ({@code
     * Generator.readBack}), as {@link AtItsKey} is. The innermost container and not the outermost:
     * the containers around it are another element's, and a row writing one value inside them
     * holds the elements of the others it writes as it writes any position under them.
     */
    record UnderItsKey(NumericTerm.GatheredUnderItsKey term) implements OfANumber {

        @Override
        public TermPath writeRoot() {
            return term.elements().containersHoldingIt().getLast();
        }

        @Override
        public String toString() {
            return term.toString();
        }
    }

    /**
     * What the elements of the key an input holds come to, realized as {@link UnderItsKey} is,
     * with every element written holding that key.
     *
     * <p>The key is another parameter's and is fixed with the rest of the row, so the elements
     * are written holding it; elements of other keys are the row's other containers', and a key
     * no element holds is a row none of them holds it at, which the number is not read for.
     */
    record UnderAKey(NumericTerm.GatheredUnderAKey term) implements OfANumber {

        @Override
        public TermPath writeRoot() {
            return term.subjectPath().containersHoldingIt().getLast();
        }

        @Override
        public TermPath keyAskedFor() {
            return term.asked();
        }

        @Override
        public boolean keyIsTheNumber() {
            return term.keyIsEachElementsNumber();
        }

        @Override
        public AskedKey askedKey() {
            return new AskedKey(term.gathered().elements(),
                    term.gathered().key().from(term.gathered().elements()), term.asked());
        }

        @Override
        public String toString() {
            return term.toString();
        }
    }

    /**
     * How many elements of a container meet a statement, realized by writing the container with
     * that many of them meeting it.
     *
     * <p>The place a search fixes for this is the count, and it says nothing about which elements:
     * the same count is met by many containers, and which of them a row holds is the composing's
     * choice ({@link CardinalityComposer}). A number the statement reads beside an element is a
     * number of the row and a target of its own.
     *
     * <p>Rooted where a number taken over the elements is, for the same reason: the container's
     * elements stand inside the outermost container holding them, and rebuilding that is what moves
     * the count.
     */
    record ACount(CountedElements count) implements RealizationTarget {

        public ACount {
            if (count == null) {
                throw new IllegalArgumentException("a count of nothing is no demand");
            }
        }

        @Override
        public TermPath writeRoot() {
            return count.container().element().outermostContainer();
        }

        /** The key the elements counted have, where they are counted for having the value an
         *  input holds for the field that is their key. */
        @Override
        public AskedKey askedKey() {
            List<TermPath> equal = Proposition.positionsHeldEqual(count.meeting());
            if (equal == null
                    || equal.get(0).insideAContainer() == equal.get(1).insideAContainer()) {
                return null;
            }
            TermPath inside = equal.get(0).insideAContainer() ? equal.get(0) : equal.get(1);
            return new AskedKey(count.container().element(), inside,
                    inside == equal.get(0) ? equal.get(1) : equal.get(0));
        }

        @Override
        public TermPath keyAskedFor() {
            AskedKey key = askedKey();
            return key == null ? null : key.asked();
        }

        @Override
        public String toString() {
            return count.toString();
        }
    }

    /**
     * A statement about the elements of a container taken together, realized by writing the
     * container so that its elements meet it — one of several ways, which ways are the statement's
     * and which one the elements meet is the composing's choice ({@link CardinalityComposer}).
     *
     * <p>Where a condition on the way came out one of more ways than are looked along one at a
     * time, and every way is something the elements of one container meet: a row meets one of them
     * where the container meets the statement, so the container is composed against the statement
     * whole and no way is chosen first.
     *
     * <p>The place a search fixes for this is one, the statement holding: nothing about it is a
     * number of the row, and what it asks is the container's elements and nothing else.
     *
     * @param behavior  the behavior whose input the statement reads, which says which order each
     *                  number it reads is on
     * @param container the container whose elements the statement is about, a parameter's own
     * @param stated    the statement, about nothing but that container and its elements
     */
    record ElementsMeetingTogether(String behavior, TermPath container, Proposition stated)
            implements RealizationTarget {

        public ElementsMeetingTogether {
            if (behavior == null || container == null || stated == null) {
                throw new IllegalArgumentException(
                        "a statement about a container's elements is some statement about one");
            }
        }

        /**
         * What {@code several}, a condition of several ways, states as a statement the elements of
         * one container meet together — or empty where no one proposition states it, where a row
         * cannot be asked it, or where it reads anything but the elements of one container a
         * parameter is. A narrowing to several cases states which case one value is, which is
         * none of these.
         *
         * @param behavior the behavior whose input the statement reads
         */
        public static Optional<ElementsMeetingTogether> of(String behavior, OnTheWay several) {
            Proposition stated = switch (several) {
                case OnTheWay.OneOf oneOf -> oneOf.stated().orElse(null);
                case OnTheWay.Counted counted -> counted.stated();
                default -> null;
            };
            if (stated == null || !AStatementAtARow.askable(stated)) {
                return Optional.empty();
            }
            TermPath container = AStatementAtARow.containerItIsAbout(stated);
            return container == null || !container.steps().isEmpty() ? Optional.empty()
                    : Optional.of(new ElementsMeetingTogether(behavior, container, stated));
        }

        @Override
        public TermPath writeRoot() {
            return container.element().outermostContainer();
        }

        @Override
        public String toString() {
            return container + " meeting " + stated.key();
        }
    }
}
