package souther.compiler.numeric;

import souther.compiler.numeric.NumericDomain.Bounds;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where a whole form lies, and not only where one atom does.
 *
 * <p>A reader deriving what is true of a value computed from several — a product of two factors, a
 * quotient of a sum — asks about the form it was given, and asking atom by atom and adding the
 * answers up would be a second place doing what {@link NumericDomain} already does when it proves a
 * comparison. So it is one question, answered where the differences between the atoms are read.
 */
class WhatADomainProvesOfAWholeFormTest {

    private static final String A = "a";
    private static final String B = "b";

    private static LinearForm<String> atom(String a) {
        return LinearForm.<String>atom(a);
    }

    private static LinearForm<String> num(long n) {
        return LinearForm.<String>constant(BigDecimal.valueOf(n));
    }

    private static Map<String, Granularity> whole(String... atoms) {
        Map<String, Granularity> out = new LinkedHashMap<>();
        for (String each : atoms) {
            out.put(each, Granularity.DISCRETE);
        }
        return out;
    }

    /** A form of one atom and a constant: the atom's own range, shifted. */
    @Test
    void aShiftedAtomLiesWhereItsAtomDoesPlusTheShift() {
        NumericDomain<String> d = NumericDomain.<String>top()
                .assume(atom(A).minus(num(2)), Rel.GE, whole(A));

        Bounds bounds = d.boundsOf(atom(A).plus(num(10)));

        assertEquals(Endpoint.inclusive(Count.of(12)), bounds.min());
        assertNull(bounds.max());
    }

    /** A sum of two bounded atoms, which is what asking one atom at a time cannot answer. */
    @Test
    void aSumLiesBetweenTheSumsOfItsAtomsEnds() {
        NumericDomain<String> d = NumericDomain.<String>top()
                .assume(atom(A).minus(num(1)), Rel.GE, whole(A))
                .assume(atom(A).minus(num(4)), Rel.LE, whole(A))
                .assume(atom(B).minus(num(10)), Rel.GE, whole(B))
                .assume(atom(B).minus(num(20)), Rel.LE, whole(B));

        Bounds bounds = d.boundsOf(atom(A).plus(atom(B)));

        assertEquals(Endpoint.inclusive(Count.of(11)), bounds.min());
        assertEquals(Endpoint.inclusive(Count.of(24)), bounds.max());
    }

    /**
     * A difference the domain holds as a difference, which is the shape nothing about either atom
     * alone would give.
     *
     * <p>{@code a - b <= 0} is recorded as the relation it is, and neither atom has a bound of its
     * own — so a reader adding up what is known atom by atom would come back with nothing.
     */
    @Test
    void aDifferenceIsReadThroughTheRelationRatherThanOffTheAtoms() {
        NumericDomain<String> d = NumericDomain.<String>top()
                .assume(atom(A).minus(atom(B)), Rel.LE, whole(A, B));

        Bounds bounds = d.boundsOf(atom(A).minus(atom(B)));

        assertEquals(Endpoint.inclusive(Count.of(0)), bounds.max());
        assertTrue(d.boundsOf(atom(A)).saysNothing(), "nothing bounds either atom on its own");
    }

    /** A form over an atom nothing was said about lies nowhere in particular. */
    @Test
    void aFormOverAnUnboundedAtomIsUnbounded() {
        Bounds bounds = NumericDomain.<String>top().boundsOf(atom(A));

        assertTrue(bounds.saysNothing());
    }

    /** Where the guards contradict there is no value to bound, and the domain says so rather than
     * answering with the ends of a path nothing takes. */
    @Test
    void anInfeasiblePathBoundsNothing() {
        NumericDomain<String> d = NumericDomain.<String>top()
                .assume(atom(A).minus(num(5)), Rel.GE, whole(A))
                .assume(atom(A).minus(num(1)), Rel.LE, whole(A));

        assertTrue(d.isBottom());
        assertTrue(d.boundsOf(atom(A).plus(num(3))).saysNothing());
    }
}
