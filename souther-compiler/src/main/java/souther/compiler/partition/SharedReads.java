package souther.compiler.partition;

import souther.compiler.core.Core;
import souther.compiler.inputs.ElementsMet;
import souther.compiler.inputs.HandedAnswers;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.Watched;

import java.util.ArrayList;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.function.Predicate;
import java.util.function.Supplier;

/**
 * Readings of a part kept to be taken again at another reading of the comparison that differs from
 * the first only in what the applications on the way to it handed to names the part does not ask
 * after.
 *
 * <p>What a reading comes to is kept only where taking it again would be the same reading:
 * <ul>
 * <li>it was read to the end, and nothing in what it came to stopped;
 * <li>it left alone everything that cannot be put back by taking it again, which is everything its
 *     scene calls a guard;
 * <li>it asked of the values handed to names, and of the elements, only what the one taking it
 *     again hands and finds the same ({@link InputReads#watchingWhatIsHanded},
 *     {@link ElementsMet.Footprint});
 * <li>everything it depends on that is not one of those stands the same (the scene's inputs).
 * </ul>
 * Taking it again meets the parts it met, at the end of what has been met. That is where whoever
 * takes it is collecting what it meets: a candidate at a choice owns the parts from where it
 * began, and the choice takes back out the parts of the candidates it does not keep. A part
 * already met by the reading that made it may stand in the list twice, and is one part to whoever
 * reads them. They are the parts of the reading that was made, read where it was made. A reading
 * taken costs what it cost once, and charging a reading that is taken again is left to the
 * caller.
 *
 * @param <C> the inputs of a reading, as the scene takes them
 * @param <E> what the scene must find unchanged after a reading
 * @param <M> a part a reading meets
 * @param <R> what a reading comes to
 */
final class SharedReads<C, E, M, R> {

    /** The state of the reader, as the readings kept are made and taken against it. */
    interface Scene<C, E, M> {

        /** Whether a reading made now may be kept, and one kept taken. */
        boolean mayShare();

        /** What a reading made now would depend on. */
        C inputs();

        /**
         * Whether {@code now} are the inputs {@code then} were, those of the aggregates being read
         * only where {@code askedAggregates}, and what an input holds only where the reading
         * {@code consulted} what it holds.
         */
        boolean sameInputs(C then, C now, boolean askedAggregates, int consulted);

        /**
         * Starts telling which of the inputs a reading asks after, and answers which were asked
         * after before it. A reading is kept for every state of the inputs, and taken again where
         * they are as they were; what it asked after is told to the reading it is taken in, which
         * a reading kept to be taken where an input it did not ask after stands otherwise needs
         * to know ({@code Pullback#kept}).
         */
        int startConsulting();

        /** What the reading begun by {@link #startConsulting} consulted; everything consulted
         *  before it, which is {@code before}, stays consulted. */
        int endConsulting(int before);

        /** Counts as consulted what a reading that is taken again consulted. */
        void consultAgain(int consulted);

        /** What a reading must leave alone, as it stands. */
        E guards();

        boolean sameGuards(E then, E now);

        /** The elements asked of so far. */
        ElementsMet elementsMet();

        /** How many parts have been met. */
        int metCount();

        /** The parts met from the {@code from}th on. */
        List<M> metSince(int from);

        /** Meets each of {@code parts} that is not met. */
        void meetAgain(List<M> parts);

        /** How many times the aggregates of the way being read have been asked after. */
        int aggregatesAsked();
    }

    /** A reading kept to be taken again, with what it asked of the reading it was made in. */
    private record Held<C, M, R>(InputReads at, int hash, HandedAnswers asked,
                                 ElementsMet.Footprint footprint, C inputs,
                                 boolean askedAggregates, int consulted, Object key, List<M> met,
                                 R result) {}

    /** A reading found, to be taken with {@link #take}. */
    record Found<M, R>(R result, ElementsMet.Footprint footprint, List<M> met,
                       HandedAnswers asked, InputReads at, int consulted) {}

    private final Scene<C, E, M> scene;
    private final Map<Core, List<Held<C, M, R>>> held = new IdentityHashMap<>();

    SharedReads(Scene<C, E, M> scene) {
        this.scene = scene;
    }

    /**
     * What {@code node} comes to read at {@code reads}, taken from a reading made before where
     * there is one, and otherwise made by {@code fresh}.
     *
     * @param key      what else a reading of {@code node} depends on, compared with
     *                 {@link Object#equals}
     * @param complete whether what a reading came to was read to the end
     */
    R shared(Core node, InputReads reads, Object key, Supplier<R> fresh, Predicate<R> complete) {
        return shared(node, reads, key, scene.elementsMet(), fresh, complete);
    }

    /**
     * The same, for a reading held to {@code elements} and not to the elements of the scene: one
     * that reads the parts of a form together, with elements of its own.
     */
    R shared(Core node, InputReads reads, Object key, ElementsMet elements, Supplier<R> fresh,
             Predicate<R> complete) {
        Found<M, R> found = find(node, reads, key, elements);
        return found != null ? take(found, elements)
                : read(node, reads, key, elements, fresh, complete);
    }

    /** The reading of {@code node} made before that taking it again at {@code reads} would not
     *  tell apart from reading it, or null. */
    Found<M, R> find(Core node, InputReads reads, Object key) {
        return find(node, reads, key, scene.elementsMet());
    }

    private Found<M, R> find(Core node, InputReads reads, Object key, ElementsMet elements) {
        if (!scene.mayShare()) {
            return null;
        }
        List<Held<C, M, R>> before = held.get(node);
        if (before == null) {
            return null;
        }
        int hash = reads.hashButForWhatIsHanded();
        C now = null;
        for (Held<C, M, R> one : before) {
            if (one.hash() != hash) {
                continue;
            }
            if (now == null) {
                now = scene.inputs();
            }
            // The key last: it is the dear comparison, a structural one of the program's own
            // nodes, and the state of the reader tells most of the readings kept at a node apart
            // before it is asked.
            if (scene.sameInputs(one.inputs(), now, one.askedAggregates(), one.consulted())
                    && elements.agrees(one.footprint()) && reads.handsAsAsked(one.asked())
                    && reads.sameButForWhatIsHanded(one.at())
                    && Objects.equals(one.key(), key)) {
                return new Found<>(one.result(), one.footprint(), one.met(), one.asked(), reads,
                        one.consulted());
            }
        }
        return null;
    }

    /** What a reading found comes to, with the elements it asked of told and the parts it met
     *  met, as reading it would have left them. */
    R take(Found<M, R> found) {
        return take(found, scene.elementsMet());
    }

    private R take(Found<M, R> found, ElementsMet elements) {
        found.at().takingAgain(found.asked());
        elements.takes(found.footprint());
        scene.meetAgain(found.met());
        scene.consultAgain(found.consulted());
        return found.result();
    }

    /**
     * {@code parts} with each part once, by what object it is, in the order they were met.
     *
     * <p>A reading that takes another again meets the parts of that one again, so a part met by a
     * reading held twice stands in the list as often as the reading is taken; each part of the
     * readings kept inside one another would stand in the outer list as many times as there are
     * ways down to it. It is one part to whoever reads them, and is held once.
     */
    private List<M> eachOnce(List<M> parts) {
        Set<M> seen = Collections.newSetFromMap(new IdentityHashMap<>());
        List<M> out = new ArrayList<>(parts.size());
        for (M each : parts) {
            if (seen.add(each)) {
                out.add(each);
            }
        }
        return List.copyOf(out);
    }

    /** What {@code fresh} comes to, kept where taking it again would be the same reading. */
    R read(Core node, InputReads reads, Object key, Supplier<R> fresh, Predicate<R> complete) {
        return read(node, reads, key, scene.elementsMet(), fresh, complete);
    }

    private R read(Core node, InputReads reads, Object key, ElementsMet elements,
                   Supplier<R> fresh, Predicate<R> complete) {
        if (!scene.mayShare()) {
            return fresh.get();
        }
        C inputs = scene.inputs();
        E guards = scene.guards();
        int metFrom = scene.metCount();
        int askedBefore = scene.aggregatesAsked();
        ElementsMet.Noting noting = elements.noting();
        int consultedBefore = scene.startConsulting();
        Watched<R> read;
        int consulted;
        try {
            read = reads.watchingWhatIsHanded(fresh);
        } finally {
            consulted = scene.endConsulting(consultedBefore);
        }
        ElementsMet.Footprint footprint = noting.ended(elements);
        R result = read.result();
        if (result != null && read.asked().toldApart() && footprint != null
                && scene.metCount() >= metFrom && scene.sameGuards(guards, scene.guards())
                && complete.test(result)) {
            held.computeIfAbsent(node, _ -> new ArrayList<>()).add(new Held<>(reads,
                    reads.hashButForWhatIsHanded(), read.asked(), footprint, inputs,
                    scene.aggregatesAsked() != askedBefore, consulted, key,
                    eachOnce(scene.metSince(metFrom)), result));
        }
        return result;
    }
}
