package souther.compiler.partition;

import souther.compiler.core.Core;
import souther.compiler.inputs.ElementsMet;
import souther.compiler.inputs.HandedAnswers;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.Watched;

import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
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
 * Taking it again meets the parts it met that a rule set aside has since taken back out of what
 * was met, so that the parts of the comparison it is taken in include them. They are the parts of
 * the reading that was made, read where it was made. A reading taken costs what it cost once, and
 * charging a reading that is taken again is left to the caller.
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

        /** Whether {@code now} are the inputs {@code then} were, those of the aggregates being
         *  read only where {@code askedAggregates}. */
        boolean sameInputs(C then, C now, boolean askedAggregates);

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
                                 boolean askedAggregates, Object key, List<M> met, R result) {}

    /** A reading found, to be taken with {@link #take}. */
    record Found<M, R>(R result, ElementsMet.Footprint footprint, List<M> met) {}

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
        Found<M, R> found = find(node, reads, key);
        return found != null ? take(found) : read(node, reads, key, fresh, complete);
    }

    /** The reading of {@code node} made before that taking it again at {@code reads} would not
     *  tell apart from reading it, or null. */
    Found<M, R> find(Core node, InputReads reads, Object key) {
        if (!scene.mayShare()) {
            return null;
        }
        List<Held<C, M, R>> before = held.get(node);
        if (before == null) {
            return null;
        }
        int hash = reads.hashButForWhatIsHanded();
        C now = null;
        ElementsMet elements = scene.elementsMet();
        for (Held<C, M, R> one : before) {
            if (one.hash() != hash || !Objects.equals(one.key(), key)) {
                continue;
            }
            if (now == null) {
                now = scene.inputs();
            }
            if (scene.sameInputs(one.inputs(), now, one.askedAggregates())
                    && elements.agrees(one.footprint()) && reads.handsAsAsked(one.asked())
                    && reads.sameButForWhatIsHanded(one.at())) {
                return new Found<>(one.result(), one.footprint(), one.met());
            }
        }
        return null;
    }

    /** What a reading found comes to, with the elements it asked of told and the parts it met
     *  met, as reading it would have left them. */
    R take(Found<M, R> found) {
        scene.elementsMet().takes(found.footprint());
        scene.meetAgain(found.met());
        return found.result();
    }

    /** What {@code fresh} comes to, kept where taking it again would be the same reading. */
    R read(Core node, InputReads reads, Object key, Supplier<R> fresh, Predicate<R> complete) {
        if (!scene.mayShare()) {
            return fresh.get();
        }
        C inputs = scene.inputs();
        E guards = scene.guards();
        int metFrom = scene.metCount();
        int askedBefore = scene.aggregatesAsked();
        ElementsMet.Noting noting = scene.elementsMet().noting();
        Watched<R> read = reads.watchingWhatIsHanded(fresh);
        ElementsMet.Footprint footprint = noting.ended(scene.elementsMet());
        R result = read.result();
        if (result != null && read.asked().toldApart() && footprint != null
                && scene.metCount() >= metFrom && scene.sameGuards(guards, scene.guards())
                && complete.test(result)) {
            held.computeIfAbsent(node, _ -> new ArrayList<>()).add(new Held<>(reads,
                    reads.hashButForWhatIsHanded(), read.asked(), footprint, inputs,
                    scene.aggregatesAsked() != askedBefore, key,
                    List.copyOf(scene.metSince(metFrom)), result));
        }
        return result;
    }
}
