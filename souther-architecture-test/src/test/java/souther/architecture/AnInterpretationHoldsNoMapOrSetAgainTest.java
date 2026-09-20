package souther.architecture;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * {@link souther.compiler.partition.Interpretation} does not hold a {@code java.util.Map} or a
 * {@code java.util.Set} again.
 *
 * <p>{@code pins} is a {@link souther.compiler.carrier.Lookup}, which answers what a key is bound
 * to and offers no {@code keySet}, {@code entrySet} or {@code forEach} to take an order off. A
 * {@code Map} offers all three, and a {@code Map} built by copying one salts the order those hand
 * back — differently on some runs than on others — so every reader of {@code pins} has to consult
 * it by key, which is all a {@code Lookup} lets a reader do.
 *
 * <p><b>A field and not a census.</b> Once {@code pins} is a {@code Lookup}, nothing here needs to
 * watch its readers any more — a reader that reached for {@code keySet} or {@code forEach} does not
 * compile against one, so the type itself is what stops that reader from being written. What a type
 * cannot stop is the declaration going back the other way: nothing keeps a future edit from giving
 * {@code pins} a {@code Map} type again, and that edit would compile. So this reads the field back
 * and refuses it if it does ({@link MapOrSetFields}).
 *
 * <p><b>One carrier and not a list of them.</b> A set of classes this holds itself to, added to by
 * hand as more are moved, is the same defect one level up — a class moved and never added is a class
 * this stops watching without saying so. So this is about {@link souther.compiler.partition
 * .Interpretation} alone, the way a rule about a form's own coefficients is about {@code
 * CanonicalForm} alone ({@link AFormIsWalkedThroughTheOrderItsPositionsDecideTest}).
 *
 * <p><b>Transitional, and named as such.</b> This is the shape a guard takes while only some of a
 * package has been moved — a rule over every field {@code souther.compiler.partition} declares
 * would answer about the ones still to move as much as about this one, and would be red from the
 * day it was written for reasons that have nothing to do with a regression. Once the whole package
 * is moved, the population becomes something the compiled output can be asked for directly —
 * every field {@code souther.compiler.partition} declares, read by {@link CompiledOutputs
 * #inTheClassesOf} — and a rule built that way replaces this file rather than standing beside it.
 * Until then, a carrier moved on its own gets a guard of its own; nothing here is meant to answer
 * for more than {@code Interpretation} in the meantime.
 */
class AnInterpretationHoldsNoMapOrSetAgainTest {

    private static final String THE_CARRIER = "souther/compiler/partition/Interpretation";

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    @Test
    void noFieldOfInterpretationIsAMapOrASet() {
        assertEquals(List.of(), MapOrSetFields.in(COMPILED.read(THE_CARRIER)),
                THE_CARRIER + " was moved off java.util.Map/Set — a field reading as one of those"
                        + " again is the same defect the move closed, and the walk a reader could"
                        + " take off it would be salted the same way");
    }
}
