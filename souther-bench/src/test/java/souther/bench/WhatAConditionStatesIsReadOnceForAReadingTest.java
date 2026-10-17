package souther.bench;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What a condition states over one reading of the input is read where that reading keeps it, and
 * by no reader for itself.
 *
 * <p>{@code WhatConditionsState} keeps, for one reading, what each truth, presence, comparison and
 * arm of a fork states, read once by the node and its names. A reader that asks {@code Pullback}
 * directly gets the same answer read again: once for each occurrence a walk writes out, each
 * application a closure is handed, and each reader that asks. Nothing in the types stops it — the
 * readings are the package's, and the one that keeps them is in the same package — so this is
 * what holds the readings to the one that keeps them.
 *
 * <p>A reading filed at a site of the model is a different question: it is the meaning of that
 * construct, said as that construct's, and is read where the meanings of a body are filed.
 *
 * <p><b>By the class.</b> The reader that keeps them calls each reading from a lambda handed to
 * its map, whose name is the compiler's; and which class may read without keeping is the rule.
 */
class WhatAConditionStatesIsReadOnceForAReadingTest {

    private static final String PULLBACK = "souther.compiler.partition.Pullback";

    /** The readings of what a condition states, as {@code Pullback} answers them. */
    private static final Set<String> READINGS = Set.of(
            "ofATruth", "ofAPresence", "ofAComparison", "ofAComparisonOnTheInput", "ofTheArms");

    /** Each class that asks {@code Pullback} what a condition states, and which readings. */
    private static final Map<String, Set<String>> READERS = new LinkedHashMap<>(Map.of(
            // Every reading of the input asks here, and is answered what every other was.
            "souther.compiler.partition.WhatConditionsState",
            Set.of("ofATruth", "ofAPresence", "ofAComparisonOnTheInput", "ofTheArms"),
            // A meaning filed at the construct it is read at, which names the site.
            "souther.compiler.partition.MeaningsOfABodyReading",
            Set.of("ofATruth", "ofTheArms")));

    @Test
    void whatAConditionStatesIsAskedOfTheReadingThatKeepsIt() {
        Map<String, Set<String>> asking = new TreeMap<>();
        for (Compiled.Site site : Compiled.sites()) {
            if (site.how() == Compiled.How.CALLS && site.owner().equals(PULLBACK)
                    && READINGS.contains(site.member()) && !outerOf(site.from()).equals(PULLBACK)) {
                asking.computeIfAbsent(outerOf(site.from()), _ -> new TreeSet<>())
                        .add(site.member());
            }
        }

        assertEquals(new TreeMap<>(READERS), asking,
                "a class reads what a condition states without the reading that keeps it, or one"
                        + " written down here stopped. Read beside it, a condition is read again for"
                        + " every occurrence, application and reader that asks, and what one reader"
                        + " was answered is not what the others were handed");
    }

    /** The class a nested or local class is written in. */
    private static String outerOf(String from) {
        int nested = from.indexOf('$');
        return nested < 0 ? from : from.substring(0, nested);
    }
}
