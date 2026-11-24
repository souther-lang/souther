package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * An entry on a way keeps its hash where it is made ({@link OnTheWay.TakenIn}), and is no other
 * value for it: equal where what it holds is equal, hashed as a record of what it holds is, and
 * written as what it holds.
 */
class AnEntryOnAWayHashesAsWhatItHoldsTest {

    private static final ConditionReportAnchor WHERE =
            new ConditionReportAnchor.WhereTheReadingMetIt("g",
                    new ConditionOccurrence("pick", ConditionOccurrence.Reading.DIVIDING, 0));

    private static RowDemand.Relational atLeast(String at) {
        return new RowDemand.Relational(new TakenConstraint.Affine(
                LinearForm.atom(new NumericTerm.ValueOf(TermPath.of(at))), Rel.GE));
    }

    /** What an entry is, as a record of it alone. */
    private record WhatItHolds(ConditionReportAnchor anchor, RowDemand.OfACondition demand,
                               NamedElements named) {}

    @Test
    void twoEntriesOfOneConditionAreOneValue() {
        OnTheWay.TakenIn one = new OnTheWay.TakenIn(WHERE, atLeast("n"), NamedElements.NONE);
        OnTheWay.TakenIn again = new OnTheWay.TakenIn(WHERE, atLeast("n"), NamedElements.NONE);

        assertEquals(one, again);
        assertEquals(one.hashCode(), again.hashCode());
        assertNotEquals(one, new OnTheWay.TakenIn(WHERE, atLeast("m"), NamedElements.NONE));
    }

    /** Hashed as a record of what it holds is, so a set of entries is laid out as it was. */
    @Test
    void anEntryIsHashedAsWhatItHolds() {
        OnTheWay.TakenIn entry = new OnTheWay.TakenIn(WHERE, atLeast("n"), NamedElements.NONE);

        assertEquals(new WhatItHolds(WHERE, atLeast("n"), NamedElements.NONE).hashCode(),
                entry.hashCode());
    }

    /** The hash is the rest's to decide: one handed in is not the one kept. */
    @Test
    void aHashHandedInIsWorkedOutAgain() {
        OnTheWay.TakenIn entry = new OnTheWay.TakenIn(WHERE, atLeast("n"), NamedElements.NONE);
        OnTheWay.TakenIn handed =
                new OnTheWay.TakenIn(WHERE, atLeast("n"), NamedElements.NONE, entry.hash() + 1);

        assertEquals(entry, handed);
        assertEquals(entry.hash(), handed.hash());
    }

    @Test
    void anEntryIsWrittenAsWhatItHolds() {
        String written =
                new OnTheWay.TakenIn(WHERE, atLeast("n"), NamedElements.NONE).toString();

        assertFalse(written.contains("hash"), written);
        assertEquals(new WhatItHolds(WHERE, atLeast("n"), NamedElements.NONE).toString()
                .replaceFirst("^WhatItHolds", "TakenIn"), written);
    }
}
