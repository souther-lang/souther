package souther.compiler.inputs;

import souther.compiler.diag.SourcePos;
import souther.compiler.types.TypeKey;

import java.util.Objects;
import java.util.Optional;

/**
 * One construction a run on the way to a rule may work out, of which neither that a run stops
 * there nor that none does is shown, and why.
 *
 * <p>Of one construction and never of the rule: another construction on the same way may be shown
 * to stop a run ({@link AConstructionStopShown}) or to stop none, and this says nothing of those.
 * Said whether or not what it asks is read, so a construction whose condition no reading takes in
 * is said here with that reason, and not left out.
 *
 * @param construction the type made, as the declaration it is: two modules may each declare one
 *                     of a name
 * @param at           where the construction is written
 * @param asked        what it asks that the way to it does not hold, or none where what it asks
 *                     is not read
 * @param why          why neither is shown
 */
public record AConstructionStopNotShown(TypeKey construction, SourcePos at,
                                        Optional<WhatAConstructionAsks.Asked> asked,
                                        WhyAConstructionStopIsNotShown why) {

    public AConstructionStopNotShown {
        if (construction == null || at == null) {
            throw new IllegalArgumentException("a construction of some type, written somewhere");
        }
        Objects.requireNonNull(asked, "what it asks, or that it is not read");
        Objects.requireNonNull(why, "a stop is not shown for some reason");
    }
}
