package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;
import java.util.OptionalInt;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Whether the string at one position is among the pieces of the string at another, the second
 * converted by case, is read off the two strings a row wrote, as the run time converts and parts
 * them.
 *
 * <p>A statement that says so can be asked of a row, and a line that decides where it holds is
 * drawn at rows that answer it. What the walk did not reach is not read, and neither answer is
 * given for it.
 */
class AStringBeingAmongThePiecesOfAnotherIsAskedOfARowTest {

    private static final TermPath DOMAIN = TermPath.of("domain");
    private static final TermPath EMAIL = TermPath.of("email");

    @Test
    void aStatementOfItIsAStatementARowAnswers() {
        assertTrue(AStatementAtARow.askable(among(1, 0)));
    }

    @Test
    void aCaseConversionIsTheRunTimes() {
        Proposition stated = among(1, 0);

        assertEquals(AStatementAtARow.Answer.HOLDS, at(stated, "example.com", "A@EXAMPLE.COM"));
        assertEquals(AStatementAtARow.Answer.FAILS, at(stated, "other.com", "A@EXAMPLE.COM"));
        assertEquals(AStatementAtARow.Answer.FAILS, at(stated.denied(), "example.com",
                "A@EXAMPLE.COM"));
    }

    @Test
    void anEmptyPieceIsAPiece() {
        assertEquals(AStatementAtARow.Answer.HOLDS, at(among(0, 0), "", "a@"));
        assertEquals(AStatementAtARow.Answer.FAILS, at(among(0, 0), "", "a"));
    }

    @Test
    void onlyThePiecesOfTheWindowAreThoseItMayBeOneOf() {
        String email = "a@b@c";

        assertEquals(AStatementAtARow.Answer.HOLDS, at(among(1, 2), "b", email));
        assertEquals(AStatementAtARow.Answer.FAILS, at(among(1, 2), "c", email));
        assertEquals(AStatementAtARow.Answer.FAILS, at(among(1, 2), "a", email));
        assertEquals(AStatementAtARow.Answer.HOLDS, at(among(1, 0), "c", email));
        assertEquals(AStatementAtARow.Answer.FAILS, at(among(5, 0), "c", email));
    }

    @Test
    void whatTheWalkDoesNotReachIsNotRead() {
        AStatementAtARow.Answer notWalked =
                new AStatementAtARow.Answer.CouldNotTell(Set.of(ReadingGap.COULD_NOT_WALK));

        assertEquals(notWalked, answered(among(1, 0), Map.of(
                EMAIL, new ObservationAtPoint.Value(new ObservedValue.Text("a@b.c")))));
        assertEquals(notWalked, answered(among(1, 0), Map.of(
                DOMAIN, new ObservationAtPoint.Value(new ObservedValue.Text("b.c")))));
    }

    private static Proposition among(int from, int until) {
        Quantity.IsAmongThePieces membership = new Quantity.IsAmongThePieces(
                new DecisionAtom.OfTheInput(new NumericTerm.ValueOf(DOMAIN)),
                ValueName.Stdlib.operation("String", "split"), OptionalInt.of('@'),
                new Quantity.WhatAnOperationAnswers(
                        ValueName.Stdlib.operation("String", "lowercase"),
                        List.of(new DecisionAtom.OfTheInput(new NumericTerm.ValueOf(EMAIL)))),
                from, until);
        return new Proposition.Compared(new Relation.Affine(
                new LinearForm<>(ExactRatio.of(-1), Map.of(membership, ExactRatio.ONE)), Rel.EQ),
                true);
    }

    private static AStatementAtARow.Answer at(Proposition stated, String domain, String email) {
        return answered(stated, Map.of(
                DOMAIN, new ObservationAtPoint.Value(new ObservedValue.Text(domain)),
                EMAIL, new ObservationAtPoint.Value(new ObservedValue.Text(email))));
    }

    private static AStatementAtARow.Answer answered(Proposition stated,
                                                    Map<TermPath, ObservationAtPoint> walked) {
        return AStatementAtARow.of(stated, "f", null).at(new AnObservationOfAForm() {

            @Override
            public WalkResult<ObservationAtPoint> at(TermPath path) {
                ObservationAtPoint there = walked.get(path);
                return there == null ? WalkResult.couldNotWalk() : WalkResult.reached(there);
            }

            @Override
            public WalkResult<List<ObservedValue>> everyValueAt(TermPath path) {
                throw new AssertionError("a string is read at its own position");
            }
        });
    }
}
