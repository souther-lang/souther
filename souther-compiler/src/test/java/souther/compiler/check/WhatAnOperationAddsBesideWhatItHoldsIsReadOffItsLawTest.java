package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.semantics.LawNumber;
import souther.compiler.semantics.LawProposition;
import souther.compiler.semantics.OperationLaw;
import souther.compiler.types.ValueName;
import souther.test.ClosedWorldContract;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Which operations a law of how many they answer says add to an argument what it does not hold
 * yet ({@link AddsWhatItDoesNotHold}), read off the laws the library states and from no list of
 * operations.
 *
 * <p>The laws are held to what the library computes elsewhere; what this holds is the reading of
 * them. An operation whose law is stated tomorrow in the same words is read the same, and this
 * names it until somebody has looked at what the reading makes of it.
 */
@ClosedWorldContract
class WhatAnOperationAddsBesideWhatItHoldsIsReadOffItsLawTest {

    @Test
    void theOperationsReadAsAddingWhatTheyDoNotHoldAreTheOnesWhoseLawSaysSo() {
        Map<String, String> read = new TreeMap<>();
        DefaultBoundOperationFacts.get().settled().forEach((operation, settled) -> {
            if (settled.get(OperationLaw.Observed.SIZE) instanceof BoundOperationFacts.Settled.ByALaw(
                    OperationLaw<DeclaredArgument> law, var _)
                    && AddsWhatItDoesNotHold.of(law) instanceof AddsWhatItDoesNotHold adds) {
                read.put(name(operation), switch (adds) {
                    case AddsWhatItDoesNotHold.OneValue one -> "holder " + one.holder().position()
                            + ", value " + one.value().position() + " among its " + one.of();
                    case AddsWhatItDoesNotHold.TheElementsOf elements -> "holder "
                            + elements.holder().position() + ", the elements of "
                            + elements.from().position();
                });
            }
        });

        // A union's law counts the elements of its second argument the first does not hold, so it
        // is read with the first as the holder and not the other way round: that the two may be
        // swapped is no law stated here.
        assertEquals(Map.of(
                "Map.insert", "holder 2, value 0 among its KEYS",
                "Map.updateOrInsert", "holder 3, value 0 among its KEYS",
                "Set.insert", "holder 1, value 0 among its ELEMENTS",
                "Set.union", "holder 0, the elements of 1"), read);
    }

    private static OperationLaw.Size<DeclaredArgument> sizeLawOf(String alias, String name) {
        BoundOperationFacts.Settled.ByALaw settled = (BoundOperationFacts.Settled.ByALaw)
                DefaultBoundOperationFacts.get().settled(ValueName.Stdlib.operation(alias, name),
                        OperationLaw.Observed.SIZE);
        return (OperationLaw.Size<DeclaredArgument>) settled.law();
    }

    /**
     * Each part of a union's law is what the reading needs: the count of the second's elements
     * that no element of the first is, and not of those that some element of the first is, and
     * that of the second's elements against the first's and not against anything else.
     */
    @Test
    void aLawThatCountsAnythingElseBesideTheHolderIsNotReadAsAddingWhatItDoesNotHold() {
        LinearForm<LawNumber<DeclaredArgument>> union =
                sizeLawOf("Set", "union").unconditional();
        LawNumber.HowManyMeet<DeclaredArgument> added = null;
        for (LawNumber<DeclaredArgument> each : union.coefs().keySet()) {
            if (each instanceof LawNumber.HowManyMeet<DeclaredArgument> meet) {
                added = meet;
            }
        }
        LawProposition.SomeElement<DeclaredArgument> none =
                (LawProposition.SomeElement<DeclaredArgument>) added.ofTheElement();
        LawProposition.Same<DeclaredArgument> same =
                (LawProposition.Same<DeclaredArgument>) none.ofTheElement();

        assertEquals(null, AddsWhatItDoesNotHold.of(new OperationLaw.Size<>(replaced(union, added,
                new LawNumber.HowManyMeet<>(added.container(), none.denied())))),
                "the elements some element of the holder is");
        assertEquals(null, AddsWhatItDoesNotHold.of(new OperationLaw.Size<>(replaced(union, added,
                new LawNumber.HowManyMeet<>(added.container(), new LawProposition.SomeElement<>(
                        none.container(), new LawProposition.Same<>(same.one(), same.one(), true),
                        false))))), "an element of the holder against itself");
        assertEquals(null, AddsWhatItDoesNotHold.of(new OperationLaw.Size<>(replaced(union, added,
                new LawNumber.HowManyMeet<>(added.container(), new LawProposition.SomeElement<>(
                        none.container(), same.denied(), false))))),
                "an element of the holder no element of the other is");
    }

    /** A set given a value holds one more only where it did not hold it: the two cases the other
     *  way round are no such law. */
    @Test
    void casesThatAddOneWhereTheValueIsHeldAreNotReadAsAddingWhatItDoesNotHold() {
        OperationLaw.Size<DeclaredArgument> insert = sizeLawOf("Set", "insert");
        List<OperationLaw.Size.Case<DeclaredArgument>> swapped = List.of(
                new OperationLaw.Size.Case<>(insert.cases().get(0).where(),
                        insert.cases().get(1).equalTo()),
                new OperationLaw.Size.Case<>(insert.cases().get(1).where(),
                        insert.cases().get(0).equalTo()));

        assertEquals(null, AddsWhatItDoesNotHold.of(new OperationLaw.Size<>(swapped)));
    }

    private static LinearForm<LawNumber<DeclaredArgument>> replaced(
            LinearForm<LawNumber<DeclaredArgument>> form, LawNumber<DeclaredArgument> part,
            LawNumber<DeclaredArgument> with) {
        Map<LawNumber<DeclaredArgument>, ExactRatio> coefs = new LinkedHashMap<>(form.coefs());
        coefs.put(with, coefs.remove(part));
        return new LinearForm<>(form.constant(), coefs);
    }

    private static String name(ValueName operation) {
        return operation instanceof ValueName.Stdlib.Operation stdlib
                ? stdlib.alias() + "." + stdlib.name() : operation.toString();
    }
}
