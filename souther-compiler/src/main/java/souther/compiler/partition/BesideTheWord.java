package souther.compiler.partition;

import souther.compiler.inputs.TermPath;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.SequencedMap;

/**
 * What else was true of a search that wrote no row, beside the word it came back with.
 *
 * <p>Two things, and a reader of one of them reads the other: the rules about a position's strings
 * that gave the offer no value, and where the runs of the rows composed stopped without answering.
 * They are one value so that what a reader shows, and what two searches are compared by, is all of
 * it wherever either is read. Held apart inside it, because they say different things about the
 * search: an offer short of what the rules leave is a search that did not try everything, and a
 * run that stopped is a row that was tried.
 *
 * @param shortOf what the rules about a position's strings left out of the offer, under the
 *                position
 * @param stopped where the runs of the rows composed stopped, each once, in the order they were met
 */
public record BesideTheWord(SequencedMap<TermPath, StringOfferShortfall> shortOf,
                            List<WhereARunStopped> stopped) {

    /** Nothing beside the word. */
    public static final BesideTheWord NOTHING = new BesideTheWord(new LinkedHashMap<>(), List.of());

    public BesideTheWord {
        // Copied, because two of these are equal by what they hold and a caller keeping what it
        // handed in could change what one of them is after it was made.
        shortOf = Collections.unmodifiableSequencedMap(new LinkedHashMap<>(shortOf));
        stopped = List.copyOf(new LinkedHashSet<>(stopped));
    }

    /** Only what the offer was short of. */
    public static BesideTheWord shortOf(SequencedMap<TermPath, StringOfferShortfall> shortOf) {
        return new BesideTheWord(shortOf, List.of());
    }

    /** The same, with where the runs stopped as well. */
    public BesideTheWord stopping(Collection<WhereARunStopped> where) {
        List<WhereARunStopped> both = new ArrayList<>(stopped);
        both.addAll(where);
        return new BesideTheWord(shortOf, both);
    }

    /** Whether there is nothing beside the word. */
    public boolean isEmpty() {
        return shortOf.isEmpty() && stopped.isEmpty();
    }
}
