package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.Case;
import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.ACarriedValue;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.meaning.WhyUnread;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;

import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A statement read of one value of a set's element at a time bounds how many elements meet it only
 * where what it says of an element is the same whatever else the set holds.
 *
 * <p>Asked of the forms directly, since no model written today has a count of a set's elements read
 * with one of the others. Those read beyond the element — the last element holding a value, a
 * quantifier over a container, how often a value occurs in one, a position outside the element —
 * and the ones reading the set the element is in fail at a set of that element alone where a set
 * of more meets them, so the end would refuse points a row stands at.
 */
class AStatementBoundsACountOnlyWhereItSaysOnlyOfTheElementTest {

    private static final TermPath XS = TermPath.of("xs");
    private static final TermPath ELEMENT = XS.element();
    private static final TermPath N = ELEMENT.then("n");
    private static final TermPath C = ELEMENT.then("c");
    private static final TermPath B = TermPath.of("b");
    private static final TermPath K = ELEMENT.then("k");
    private static final CasesLeft HOT = CasesLeft.ofEach(List.of(Refinement.of(new Case.SumCase(
            TypeSymbols.declared(new TypeKey("probe", "Hot")), true))));

    @Test
    void eachFormIsTheElementsOwnOrNot() {
        record Case(Proposition stated, boolean element) {}
        for (Case each : List.of(
                new Case(new Proposition.Always(true), true),
                new Case(truth(N), true),
                new Case(new Proposition.Present(new DecisionSubject.AnInput(N), true), true),
                new Case(new Proposition.SameValue(new DecisionSubject.AnInput(N),
                        new DecisionSubject.AnInput(C), true), true),
                new Case(Proposition.all(List.of(truth(N), truth(C))), true),
                new Case(Proposition.any(List.of(truth(N), truth(C))), true),
                new Case(new Proposition.InCases(new DecisionSubject.AnInput(K), HOT, true), true),
                new Case(compared(new NumericTerm.ValueOf(N)), true),
                new Case(ordered(new NumericTerm.ValueOf(N)), true),
                new Case(new Proposition.InCases(new DecisionSubject.AnInput(B), HOT, true), false),
                new Case(ordered(new NumericTerm.ValueOf(B)), false),
                new Case(ordered(NumericTerm.Multiplicity.of(XS, N)), false),
                new Case(new Proposition.OnAnApplication(List.of(truth(N), truth(C))), false),
                new Case(new Proposition.SomeReachable(N, N, List.of("next"), truth(N),
                        Optional.empty(), true), false),
                new Case(new Proposition.Unread(Optional.empty(), 0,
                        new WhyUnread.NotMetByTheReading(), false, true), false),
                new Case(new Proposition.Carried(ACarriedValue.made(), true), false),
                new Case(truth(B), false),
                new Case(Proposition.any(List.of(truth(N), truth(B))), false),
                new Case(new Proposition.SameValue(new DecisionSubject.AnInput(N),
                        new DecisionSubject.AnInput(B), true), false),
                new Case(compared(new NumericTerm.ValueOf(B)), false),
                new Case(compared(NumericTerm.Multiplicity.of(XS, N)), false),
                new Case(new Proposition.LastToHold(XS, N, true), false),
                new Case(new Proposition.Some(new DecisionSubject.AnInput(XS), truth(N), true),
                        false))) {
            assertEquals(each.element(), HowManyCanMeet.saysOnlyOfTheElement(each.stated(),
                    ELEMENT), each.stated().key());
        }
    }

    private static Proposition truth(TermPath at) {
        return new Proposition.Truth(new DecisionSubject.AnInput(at), true);
    }

    private static Proposition ordered(NumericTerm term) {
        return new Proposition.Compared(new Relation.Ordered(new DecisionAtom.OfTheInput(term),
                Count.of(2), Rel.GT), true);
    }

    private static Proposition compared(NumericTerm term) {
        return new Proposition.Compared(new Relation.Affine(new LinearForm<Quantity>(
                ExactRatio.of(-2), Map.of(new DecisionAtom.OfTheInput(term), ExactRatio.ONE)),
                Rel.GT), true);
    }
}
