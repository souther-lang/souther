package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.proof.Slot;
import souther.compiler.semantics.LawNumber;
import souther.compiler.semantics.LawProposition;
import souther.compiler.semantics.LawSubject;
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

    /**
     * Read where a law of how many says so and a law of what the answer holds says the same
     * values: an insert, of a value or under a key, whether the library declares it or proves it
     * of a body that inserts on either arm, and a union, whose law of how many counts the
     * elements of its second argument the first does not hold, with the first as the holder.
     * Every operation counted so is read.
     */
    @Test
    void theOperationsReadAsAddingWhatTheyDoNotHoldAreTheOnesWhoseLawsSaySo() {
        Map<String, String> read = new TreeMap<>();
        Map<String, String> counted = new TreeMap<>();
        BoundOperationFacts facts = DefaultBoundOperationFacts.get();
        facts.settled().forEach((operation, settled) -> {
            if (settled.get(OperationLaw.Observed.SIZE) instanceof BoundOperationFacts.Settled.ByALaw(
                    OperationLaw<DeclaredArgument> law, var _)
                    && AddsWhatItDoesNotHold.countedBy(law) instanceof AddsWhatItDoesNotHold adds) {
                counted.put(name(operation), said(adds));
            }
            if (facts.addsWhatItDoesNotHold(operation) instanceof AddsWhatItDoesNotHold adds) {
                read.put(name(operation), said(adds));
            }
        });

        assertEquals(Map.of(
                "Map.insert", "holder 2, value 0 among its KEYS",
                "Map.updateOrInsert", "holder 3, value 0 among its KEYS",
                "Set.insert", "holder 1, value 0 among its ELEMENTS",
                "Set.union", "holder 0, the elements of 1"), read);
        assertEquals(counted, read);
    }

    /**
     * A union's law of membership says a value is in its answer where either set holds it; one
     * saying so of the first alone, or of a set it was not handed, is not what the count adds.
     */
    @Test
    void aUnionsMembershipLawIsReadWithBothItsSets() {
        ValueName union = ValueName.Stdlib.operation("Set", "union");
        OperationLaw.Size<DeclaredArgument> size = sizeLawOf("Set", "union");
        List<LawProposition<Slot>> stated = DefaultBoundOperationFacts.get().relationsOf(union);
        assertEquals(AddsWhatItDoesNotHold.countedBy(size),
                AddsWhatItDoesNotHold.of(union, size, stated));
        assertEquals(null, AddsWhatItDoesNotHold.of(union, size, List.of()), "how many alone");
        assertEquals(null, AddsWhatItDoesNotHold.of(union, size,
                stated.stream().map(each -> swapped(each, 1, 2)).toList()),
                "a set it was not handed");
    }

    private static String said(AddsWhatItDoesNotHold adds) {
        return switch (adds) {
            case AddsWhatItDoesNotHold.OneValue one -> "holder " + one.holder().position()
                    + ", value " + one.value().position() + " among its " + one.of();
            case AddsWhatItDoesNotHold.TheElementsOf elements -> "holder "
                    + elements.holder().position() + ", the elements of "
                    + elements.from().position();
        };
    }

    /**
     * What the answer holds is read off the law of membership in the same words as the law of how
     * many: a membership law about the holder at another argument, or about another value, is not
     * what the count adds.
     */
    @Test
    void aMembershipLawOfOtherValuesIsNotWhatTheCountAdds() {
        ValueName insert = ValueName.Stdlib.operation("Set", "insert");
        OperationLaw.Size<DeclaredArgument> size = sizeLawOf("Set", "insert");
        List<LawProposition<Slot>> stated = DefaultBoundOperationFacts.get().relationsOf(insert);
        assertEquals(AddsWhatItDoesNotHold.countedBy(size),
                AddsWhatItDoesNotHold.of(insert, size, stated));
        assertEquals(null, AddsWhatItDoesNotHold.of(insert, size, List.of()),
                "how many alone");
        assertEquals(null, AddsWhatItDoesNotHold.of(ValueName.Stdlib.operation("Set", "union"),
                size, stated), "of another operation's answer");
        assertEquals(null, AddsWhatItDoesNotHold.of(insert, size,
                stated.stream().map(each -> swapped(each, 0, 1)).toList()),
                "the value and the holder the other way round");
        assertEquals(null, AddsWhatItDoesNotHold.of(insert, size,
                stated.stream().map(each -> anotherValue(each, 7)).toList()),
                "what the holder held and another value than the one handed");
    }

    /** {@code stated} with every value said to be the same as another said to be the same as the
     *  argument at {@code at} instead. */
    private static LawProposition<Slot> anotherValue(LawProposition<Slot> stated, int at) {
        return switch (stated) {
            case LawProposition.Any<Slot>(var parts) ->
                    new LawProposition.Any<>(parts.stream().map(p -> anotherValue(p, at))
                            .toList());
            case LawProposition.All<Slot>(var parts) ->
                    new LawProposition.All<>(parts.stream().map(p -> anotherValue(p, at))
                            .toList());
            case LawProposition.Same<Slot>(var a, var b, boolean holds) ->
                    new LawProposition.Same<>(a,
                            new LawSubject.Argument<>(new Slot.Place(at)), holds);
            default -> stated;
        };
    }

    /** {@code stated} with the arguments at {@code one} and {@code other} trading places
     *  wherever it names them by place. */
    private static LawProposition<Slot> swapped(LawProposition<Slot> stated, int one, int other) {
        return switch (stated) {
            case LawProposition.Any<Slot>(var parts) ->
                    new LawProposition.Any<>(parts.stream().map(p -> swapped(p, one, other))
                            .toList());
            case LawProposition.All<Slot>(var parts) ->
                    new LawProposition.All<>(parts.stream().map(p -> swapped(p, one, other))
                            .toList());
            case LawProposition.Same<Slot>(var a, var b, boolean holds) ->
                    new LawProposition.Same<>(swapped(a, one, other), swapped(b, one, other),
                            holds);
            case LawProposition.Observed<Slot>(var of, var side) ->
                    new LawProposition.Observed<>(swapped(of, one, other), side);
            default -> stated;
        };
    }

    private static LawSubject<Slot> swapped(LawSubject<Slot> subject, int one, int other) {
        return switch (subject) {
            case LawSubject.Argument<Slot>(Slot.Place(int at)) -> new LawSubject.Argument<>(
                    new Slot.Place(at == one ? other : at == other ? one : at));
            // The answer named is the operation's handed its own arguments, which stays so.
            case LawSubject.AnswerOf<Slot>(var operation, var args)
                    when operation.name().equals("contains") -> new LawSubject.AnswerOf<>(
                    operation, args.stream().map(each -> swapped(each, one, other)).toList());
            default -> subject;
        };
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

        assertEquals(null, AddsWhatItDoesNotHold.countedBy(new OperationLaw.Size<>(replaced(union, added,
                new LawNumber.HowManyMeet<>(added.container(), none.denied())))),
                "the elements some element of the holder is");
        assertEquals(null, AddsWhatItDoesNotHold.countedBy(new OperationLaw.Size<>(replaced(union, added,
                new LawNumber.HowManyMeet<>(added.container(), new LawProposition.SomeElement<>(
                        none.container(), new LawProposition.Same<>(same.one(), same.one(), true),
                        false))))), "an element of the holder against itself");
        assertEquals(null, AddsWhatItDoesNotHold.countedBy(new OperationLaw.Size<>(replaced(union, added,
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

        assertEquals(null, AddsWhatItDoesNotHold.countedBy(new OperationLaw.Size<>(swapped)));
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
