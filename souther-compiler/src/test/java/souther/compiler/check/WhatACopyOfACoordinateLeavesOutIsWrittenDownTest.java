package souther.compiler.check;

import org.junit.jupiter.api.Test;

import java.lang.reflect.RecordComponent;
import java.util.LinkedHashSet;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A record built by copying fields out of another says which it left behind.
 *
 * <p>{@code FieldDomains.Unread} is written from a coordinate the reading found, one field at a
 * time, because the coordinate is this class's own and the record crosses into {@code inputs}. Two
 * of its fields went in one round late apiece — first whether the position is a count, then which
 * conjunct the reason came from — each after something downstream turned out to need what the
 * producer already had, and each looked like an unrelated fix.
 *
 * <p>So what the copy leaves out is written down rather than discovered. A field added to the
 * coordinate fails here, which is the point: the answer may well be that the copy does not want it,
 * and that is a decision somebody makes rather than a thing nobody noticed.
 */
class WhatACopyOfACoordinateLeavesOutIsWrittenDownTest {

    private static Set<String> componentsOf(Class<?> of) {
        Set<String> out = new LinkedHashSet<>();
        for (RecordComponent each : of.getRecordComponents()) {
            out.add(each.getName());
        }
        return out;
    }

    /** The reading's coordinate, which is package-private and reached by name. */
    private static Class<?> coordinate() {
        for (Class<?> each : InvariantChecker.class.getDeclaredClasses()) {
            if (each.getSimpleName().equals("Coordinate")) {
                return each;
            }
        }
        throw new AssertionError("the reading no longer has a coordinate");
    }

    /**
     * Every field of the coordinate is carried, except the carrier, which nothing has asked for.
     *
     * <p>Not a rule that a copy must be whole. A copy that leaves something out is fine and is often
     * right; what is not fine is nobody knowing which. The carrier is what a position's values are
     * ordered on, and no reader of an unread rule has wanted it — a reader that does will find it
     * here rather than in a round of its own.
     */
    @Test
    void theCopyCarriesEveryFieldOfTheCoordinateButTheCarrier() {
        Set<String> left = new LinkedHashSet<>(componentsOf(coordinate()));
        left.removeAll(componentsOf(FieldDomains.Unread.class));

        assertEquals(Set.of("carrier"), left,
                "a field of the coordinate that the copy does not carry, and nobody decided to");
    }

    /** And what it adds is what the copy is for: whose rule it is, and which conjunct. */
    @Test
    void andWhatItAddsIsWhatTheCopyIsFor() {
        Set<String> added = new LinkedHashSet<>(componentsOf(FieldDomains.Unread.class));
        added.removeAll(componentsOf(coordinate()));

        assertEquals(Set.of("from", "part", "why"), added);
        assertTrue(componentsOf(FieldDomains.Unread.class).containsAll(Set.of("path", "measured")),
                "beside the two of the coordinate that a reader downstream turned out to need");
    }
}
