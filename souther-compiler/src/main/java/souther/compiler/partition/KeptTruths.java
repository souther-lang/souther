package souther.compiler.partition;

import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.ReadMeaning;
import souther.compiler.meaning.Proposition;

import java.util.ArrayList;
import java.util.List;

/**
 * Which occurrences of a container written out are there on some row: each thing an occurrence was
 * kept by — a truth, or an arm a run takes — read where it was decided
 * ({@link WhatConditionsState#kept}).
 *
 * <p>The one decision every reader of an occurrence takes. A truth that holds on no row drops the
 * occurrence for every reader alike — no run hands it to a closure, nothing stated of it is part of
 * a statement about some element or of a count of them, and no value of it is one a name takes —
 * and one that holds on every row is no condition. Decided by each reader for itself, one would
 * read an application another had left out, and a reading that stopped on an element no run has
 * would stop the elements that are there.
 */
final class KeptTruths {

    private KeptTruths() {
    }

    /** What decides, for a reading of {@code read}'s input, which occurrences are there. */
    static ReadMeaning.WhereKept readIn(InputReading read) {
        return keptWhere -> stillOpen(keptWhere, read);
    }

    private static List<ReadMeaning.Occurrence.Kept> stillOpen(
            List<ReadMeaning.Occurrence.Kept> keptWhere, InputReading read) {
        if (keptWhere.isEmpty()) {
            return keptWhere;
        }
        List<ReadMeaning.Occurrence.Kept> out = new ArrayList<>();
        for (ReadMeaning.Occurrence.Kept kept : keptWhere) {
            switch (WhatConditionsState.of(read).kept(kept, read)) {
                case Proposition.Always(boolean holds) when !holds -> {
                    return null;
                }
                case Proposition.Always _ -> { }
                case Proposition.Compared _, Proposition.Truth _, Proposition.InCases _,
                     Proposition.Present _, Proposition.SameValue _, Proposition.LastToHold _,
                     Proposition.All _, Proposition.Any _, Proposition.Some _,
                     Proposition.Carried _, Proposition.SomeReachable _, Proposition.Unread _,
                     Proposition.OnAnApplication _, Proposition.SoManyHold _ -> out.add(kept);
            }
        }
        return out.size() == keptWhere.size() ? keptWhere : out;
    }
}
