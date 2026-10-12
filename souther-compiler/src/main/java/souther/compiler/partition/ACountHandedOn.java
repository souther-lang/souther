package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Place;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.OptionalInt;

/**
 * A count of the elements of a container meeting a statement that holds of another container: that
 * some entry of it is keyed by the element, or that some element of it is the element's value —
 * or, the other way round, that none is.
 *
 * <p>Whether an element meets such a statement is not the element's to say. It is what the other
 * container holds, and that is composed after the counted one, out of what the counted one was
 * built as — so how many elements meet it is chosen, and handed on as what the other container is
 * to hold for each of them ({@link ContentsAsked}). What the other container is asked is what the
 * reading of the statement said an element meeting it asks ({@link CountedElements#handedOn}),
 * written the way every demand on a container inside an element is ({@link ContentsAsked#within}).
 *
 * <p><b>Chosen once, off what the count is asked at.</b> Which count a container is composed at is
 * the number the search is walking ({@link AskedAt#walked}) — the one a caller named where it named
 * one — and not the numbers a search is about, which a walk of one number out of them says nothing
 * of the rest of. The counted container is composed with that many elements meeting the statement
 * and the other container is handed exactly that, both by {@link #counted} on the one value, so the
 * two compose one row.
 *
 * <p><b>The first so many meet it and the rest do not.</b> A container of more elements than are
 * counted holds the statement for its first elements, in the order it holds them, and its denial for
 * the others. Elements equal at what the other container is asked about cannot be on both sides, so
 * the composer asks for elements no two of which are equal where both sides hold some
 * ({@link Witnesses#apart}).
 *
 * @param counted the container whose elements are counted
 * @param meeting what the other container is asked about an element meeting the statement
 */
record ACountHandedOn(TermPath counted, RowDemand.WithinIt meeting) {

    private static final int MOST_ELEMENTS =
            CompositionBudget.ELEMENTS_A_COUNT_IS_COMPOSED_WITH.maximum();

    ACountHandedOn {
        Objects.requireNonNull(counted, "a count is of the elements of some container");
        Objects.requireNonNull(meeting, "an element meeting it asks something of a container");
    }

    /**
     * What {@code count} hands on, where what an element meeting it asks is one demand on another
     * container that a container is written for — holding the value, or holding none equal to it —
     * so that its denial is one too. Nothing otherwise.
     *
     * <p>Another container and not one inside the counted element. One inside it is written where
     * the counted container is, alike in every element, and the first so many holding the value
     * and the rest none equal to it is no element written alike; nor is one around the counted
     * container, which is composed out of its elements and not after them.
     */
    static Optional<ACountHandedOn> of(CountedElements count) {
        return count.handedOn().flatMap(meeting -> of(count.container(), meeting));
    }

    /** What a count of the elements of {@code counted}, an element meeting which asks
     *  {@code meeting}, hands on ({@link #of(CountedElements)}). */
    static Optional<ACountHandedOn> of(TermPath counted, RowDemand.WithinIt meeting) {
        if (!composed(meeting) || meeting.container().isAtOrUnder(counted.element())
                || counted.isAtOrUnder(meeting.container().element())) {
            return Optional.empty();
        }
        return Optional.of(new ACountHandedOn(counted, meeting));
    }

    /**
     * Whether {@code within} is a demand a container is written for: some element of it the value,
     * or every element of it apart from the value.
     */
    private static boolean composed(RowDemand.WithinIt within) {
        return switch (within.asked()) {
            case RowDemand.SameAs _, RowDemand.KeyedAs _ -> within.some();
            case RowDemand.DifferentFrom _, RowDemand.NotKeyedAs _ -> !within.some();
            case RowDemand.Relational _, RowDemand.ATruth _, RowDemand.InCases _,
                 RowDemand.WithinIt _ -> false;
        };
    }

    /**
     * The fields from the counted element to the value the other container is asked about, in the
     * order they are taken — none where it is the element itself — or null where the way there
     * takes a step that is no field.
     */
    List<String> fieldsToTheValue() {
        TermPath value = switch (meeting.asked()) {
            case RowDemand.SameAs(TermPath at) -> at;
            case RowDemand.DifferentFrom(TermPath at) -> at;
            case RowDemand.KeyedAs(TermPath at) -> at;
            case RowDemand.NotKeyedAs(TermPath at) -> at;
            case RowDemand.Relational _, RowDemand.ATruth _, RowDemand.InCases _,
                 RowDemand.WithinIt _ -> throw new IllegalStateException(
                    "a demand handed on is one a container is written for: " + meeting);
        };
        TermPath element = counted.element();
        if (!value.isAtOrUnder(element)) {
            return null;
        }
        List<String> out = new ArrayList<>();
        for (TermPath.Step step : value.steps().subList(element.steps().size(),
                value.steps().size())) {
            if (!(step instanceof TermPath.Step.Field(String name))) {
                return null;
            }
            out.add(name);
        }
        return out;
    }

    /** What the other container is asked about an element not meeting the statement. */
    RowDemand.WithinIt denied() {
        RowDemand.OfAnElement asked = switch (meeting.asked()) {
            case RowDemand.SameAs(TermPath value) -> new RowDemand.DifferentFrom(value);
            case RowDemand.DifferentFrom(TermPath value) -> new RowDemand.SameAs(value);
            case RowDemand.KeyedAs(TermPath value) -> new RowDemand.NotKeyedAs(value);
            case RowDemand.NotKeyedAs(TermPath value) -> new RowDemand.KeyedAs(value);
            case RowDemand.Relational _, RowDemand.ATruth _, RowDemand.InCases _,
                 RowDemand.WithinIt _ -> throw new IllegalStateException(
                    "a demand handed on is one a container is written for: " + meeting);
        };
        return new RowDemand.WithinIt(meeting.container(), !meeting.some(), asked);
    }

    /**
     * How many elements meet the statement in a container composed for {@code at}: the number a
     * caller named, where it named one, and otherwise the fewest the search walks — which is the
     * one every size of container the walk allows can be composed at. Nothing where the walk holds
     * no count up to the most elements a container for a count is composed with, which is that
     * figure stopping it: the composer says so ({@link CardinalityComposer}), and nothing is
     * handed on for a container it does not compose.
     */
    static OptionalInt counted(AskedAt at) {
        Place named = at.named();
        for (int count = 0; count <= MOST_ELEMENTS; count++) {
            Count place = Count.of(count);
            if (at.walking().holds(place, Carrier.WHOLE)
                    && (named == null || named.sameAs(place))) {
                return OptionalInt.of(count);
            }
        }
        return OptionalInt.empty();
    }

    /**
     * What the other container is asked for each element of the counted one, where the first
     * {@code count} elements meet the statement and the rest do not.
     */
    List<ContentsAsked.Asked> asked(int count) {
        List<ContentsAsked.Asked> out = new ArrayList<>();
        if (count > 0) {
            out.addAll(ContentsAsked.within(meeting,
                    new ContentsAsked.Around(counted, false, 0, count)));
        }
        out.addAll(ContentsAsked.within(denied(),
                new ContentsAsked.Around(counted, false, count, Integer.MAX_VALUE)));
        return out;
    }

    /**
     * What every count among {@code asked} that hands its statement on asks of the other
     * container, at the count each is composed at.
     */
    static List<ContentsAsked.Asked> askedOf(Map<RealizationTarget, AskedAt> asked) {
        List<ContentsAsked.Asked> out = new ArrayList<>();
        asked.forEach((target, at) -> {
            if (target instanceof RealizationTarget.ACount count) {
                of(count.count()).ifPresent(handed ->
                        counted(at).ifPresent(meeting -> out.addAll(handed.asked(meeting))));
            }
        });
        return out;
    }
}
