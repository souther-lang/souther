package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What a body reads together is held as the ways that read it, and a combination is made where
 * something asks for it.
 *
 * <p>Two positions of five hundred classes each, read together in every class by one way, make a
 * quarter of a million combinations — more than a compilation lists. The reading of them is that
 * one way, and asked a class of the first at a time it answers every one of them.
 */
class WhatIsReadTogetherIsHeldAsTheWaysTest {

    private static final int CLASSES = 500;

    @Test
    void oneWayOverTwoWidePositionsIsOneWayAndAnswersEveryCombination() {
        AxisId one = new AxisId("wide", "one");
        AxisId other = new AxisId("wide", "other");
        List<String> oneClasses = classes("one");
        List<String> otherClasses = classes("other");
        BitSet every = new BitSet();
        every.set(0, CLASSES);
        ReadTogether.Read read = new ReadTogether.Read(List.of(one, other),
                List.of(oneClasses, otherClasses),
                List.of(new ReadTogether.Way(List.of(every, every), List.of(-1, -1))),
                List.of());

        assertEquals(1, read.ways().size(), "what is held is the way");
        ReadTogether.Between between = read.between(one, oneClasses, other, otherClasses);
        long combinations = 0;
        for (int here = 0; here < CLASSES; here++) {
            combinations += between.readWith(here).cardinality();
        }
        assertEquals((long) CLASSES * CLASSES, combinations);
    }

    /** Two positions of one group of case choices are read together only a choice at a time. */
    @Test
    void aWayReadsNoCombinationOfTwoPositionsItHoldsApart() {
        AxisId one = new AxisId("apart", "one");
        AxisId other = new AxisId("apart", "other");
        BitSet both = new BitSet();
        both.set(0, 2);
        ReadTogether.Read read = new ReadTogether.Read(List.of(one, other),
                List.of(List.of("a", "b"), List.of("c", "d")),
                List.of(new ReadTogether.Way(List.of(both, both), List.of(0, 0))),
                List.of());

        ReadTogether.Between between =
                read.between(one, List.of("a", "b"), other, List.of("c", "d"));
        assertEquals(0, between.readWith(0).cardinality() + between.readWith(1).cardinality());
    }

    private static List<String> classes(String of) {
        List<String> out = new ArrayList<>();
        for (int each = 0; each < CLASSES; each++) {
            out.add(of + "/" + each);
        }
        return out;
    }
}
