package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.meaning.StringsLanguage;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;
import souther.compiler.types.ValueName;

import net.unit8.notation199x.pattern.PatternParser;
import net.unit8.notation199x.pattern.PatternRead;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;
import java.util.OptionalInt;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Whether the string at one position is among the pieces of the string at another, the second
 * converted by case, and whether a string is in a language, are read off the strings a row wrote,
 * as the run time converts and parts them.
 *
 * <p>A position declared a newtype over {@code String} holds the construction, since a newtype is
 * no step of a path, and the string is the one inside it. Every row here is written both ways.
 *
 * <p>A statement that says so can be asked of a row, and a line that decides where it holds is
 * drawn at rows that answer it. What the walk did not reach is not read, and neither answer is
 * given for it. And a statement reading a string beside an element of a container is not about
 * that container alone.
 */
class AStringBeingAmongThePiecesOfAnotherIsAskedOfARowTest {

    private static final TermPath DOMAIN = TermPath.of("domain");
    private static final TermPath EMAIL = TermPath.of("email");

    private static final TermPath ACCOUNT_DOMAIN = TermPath.of("accounts").element().then("domain");

    private static final TermPath ACCOUNT_EMAIL = TermPath.of("accounts").element().then("email");

    private static final DecisionSubject ACCOUNTS =
            new DecisionSubject.AnInput(TermPath.of("accounts"));

    private static final StringsLanguage LOWERCASE_LETTERS = new StringsLanguage(
            ((PatternRead.Read) PatternParser.read("[a-z]+")).meaning());

    @Test
    void aStatementOfItIsAStatementARowAnswers() {
        assertTrue(AStatementAtARow.askable(among(DOMAIN, EMAIL, 1, 0)));
        assertTrue(AStatementAtARow.askable(inLanguage(DOMAIN)));
    }

    @Test
    void aCaseConversionIsTheRunTimes() {
        Proposition stated = among(DOMAIN, EMAIL, 1, 0);

        for (boolean wrapped : List.of(false, true)) {
            assertEquals(AStatementAtARow.Answer.HOLDS,
                    at(stated, "example.com", "A@EXAMPLE.COM", wrapped));
            assertEquals(AStatementAtARow.Answer.FAILS,
                    at(stated, "other.com", "A@EXAMPLE.COM", wrapped));
            assertEquals(AStatementAtARow.Answer.FAILS,
                    at(stated.denied(), "example.com", "A@EXAMPLE.COM", wrapped));
        }
    }

    @Test
    void anEmptyPieceIsAPiece() {
        assertEquals(AStatementAtARow.Answer.HOLDS, at(among(DOMAIN, EMAIL, 0, 0), "", "a@", true));
        assertEquals(AStatementAtARow.Answer.FAILS, at(among(DOMAIN, EMAIL, 0, 0), "", "a", true));
    }

    @Test
    void onlyThePiecesOfTheWindowAreThoseItMayBeOneOf() {
        String email = "a@b@c";

        assertEquals(AStatementAtARow.Answer.HOLDS,
                at(among(DOMAIN, EMAIL, 1, 2), "b", email, true));
        assertEquals(AStatementAtARow.Answer.FAILS,
                at(among(DOMAIN, EMAIL, 1, 2), "c", email, true));
        assertEquals(AStatementAtARow.Answer.FAILS,
                at(among(DOMAIN, EMAIL, 1, 2), "a", email, true));
        assertEquals(AStatementAtARow.Answer.HOLDS,
                at(among(DOMAIN, EMAIL, 1, 0), "c", email, true));
        assertEquals(AStatementAtARow.Answer.FAILS,
                at(among(DOMAIN, EMAIL, 5, 0), "c", email, true));
    }

    @Test
    void aStringInALanguageIsReadInsideTheNewtypeItIsWrittenIn() {
        Proposition stated = inLanguage(DOMAIN);

        for (boolean wrapped : List.of(false, true)) {
            assertEquals(AStatementAtARow.Answer.HOLDS, at(stated, "abc", "", wrapped));
            assertEquals(AStatementAtARow.Answer.FAILS, at(stated, "ab1", "", wrapped));
            assertEquals(AStatementAtARow.Answer.FAILS,
                    at(stated.denied(), "abc", "", wrapped));
        }
    }

    @Test
    void whatTheWalkDoesNotReachIsNotRead() {
        AStatementAtARow.Answer notWalked =
                new AStatementAtARow.Answer.CouldNotTell(Set.of(ReadingGap.COULD_NOT_WALK));

        assertEquals(notWalked, answered(among(DOMAIN, EMAIL, 1, 0), Map.of(
                EMAIL, new ObservationAtPoint.Value(new ObservedValue.Text("a@b.c")))));
        assertEquals(notWalked, answered(among(DOMAIN, EMAIL, 1, 0), Map.of(
                DOMAIN, new ObservationAtPoint.Value(new ObservedValue.Text("b.c")))));
        assertEquals(notWalked, answered(inLanguage(DOMAIN), Map.of()));
    }

    @Test
    void aValueThatIsNoStringIsNotRead() {
        AStatementAtARow.Answer noString = new AStatementAtARow.Answer.CouldNotTell(
                Set.of(ReadingGap.NO_VALUE));

        assertEquals(noString, answered(inLanguage(DOMAIN), Map.of(
                DOMAIN, new ObservationAtPoint.Value(new ObservedValue.Integer(3)))));
    }

    @Test
    void aRowThatWroteNothingThereIsOnNeitherSide() {
        Map<TermPath, ObservationAtPoint> wrote = Map.of(DOMAIN, ObservationAtPoint.WROTE_NOTHING,
                EMAIL, new ObservationAtPoint.Value(new ObservedValue.Text("a@b.c")));

        assertEquals(AStatementAtARow.Answer.FAILS, answered(among(DOMAIN, EMAIL, 1, 0), wrote));
        assertEquals(AStatementAtARow.Answer.FAILS,
                answered(among(DOMAIN, EMAIL, 1, 0).denied(), wrote));
    }

    /**
     * Both strings beside the element are not the element's alone: a statement that some account's
     * domain is a piece of an address no account holds is about the accounts and that address.
     * Taken for one about the accounts, the address would be composed as though it were a part of
     * each account.
     */
    @Test
    void aStringBesideTheElementIsNoStringOfTheContainerAlone() {
        Proposition beside = new Proposition.Some(ACCOUNTS,
                among(ACCOUNT_DOMAIN, EMAIL, 1, 0), true);
        Proposition within = new Proposition.Some(ACCOUNTS,
                among(ACCOUNT_DOMAIN, ACCOUNT_EMAIL, 1, 0), true);

        assertNull(AStatementAtARow.containerItIsAbout(beside));
        assertEquals(TermPath.of("accounts"), AStatementAtARow.containerItIsAbout(within));
    }

    @Test
    void aStringOfALanguageIsAPositionTheStatementReads() {
        Proposition beside = new Proposition.Some(ACCOUNTS, new Proposition.All(List.of(
                inLanguage(ACCOUNT_DOMAIN), inLanguage(EMAIL))), true);
        Proposition within = new Proposition.Some(ACCOUNTS, new Proposition.All(List.of(
                inLanguage(ACCOUNT_DOMAIN), inLanguage(ACCOUNT_EMAIL))), true);

        assertNull(AStatementAtARow.containerItIsAbout(beside));
        assertEquals(TermPath.of("accounts"), AStatementAtARow.containerItIsAbout(within));
    }

    private static Proposition inLanguage(TermPath at) {
        return new Proposition.InTheStrings(
                new Proposition.InTheStrings.Strings.AtAPosition(at), LOWERCASE_LETTERS, true);
    }

    private static Proposition among(TermPath value, TermPath string, int from, int until) {
        Quantity.IsAmongThePieces membership = new Quantity.IsAmongThePieces(
                new DecisionAtom.OfTheInput(new NumericTerm.ValueOf(value)),
                ValueName.Stdlib.operation("String", "split"), OptionalInt.of('@'),
                new Quantity.WhatAnOperationAnswers(
                        ValueName.Stdlib.operation("String", "lowercase"),
                        List.of(new DecisionAtom.OfTheInput(new NumericTerm.ValueOf(string)))),
                from, until);
        return new Proposition.Compared(new Relation.Affine(
                new LinearForm<>(ExactRatio.of(-1), Map.of(membership, ExactRatio.ONE)), Rel.EQ),
                true);
    }

    private static AStatementAtARow.Answer at(Proposition stated, String domain, String email,
                                              boolean wrapped) {
        return answered(stated, Map.of(
                DOMAIN, new ObservationAtPoint.Value(written(domain, wrapped)),
                EMAIL, new ObservationAtPoint.Value(written(email, wrapped))));
    }

    /** The string as a row writes it at a position: under the newtype the position is declared
     *  as, or as it is. */
    private static ObservedValue written(String text, boolean wrapped) {
        ObservedValue string = new ObservedValue.Text(text);
        return wrapped ? new ObservedValue.Constructed(
                TypeSymbols.declared(new TypeKey("probe", "Address")), Map.of("value", string))
                : string;
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
