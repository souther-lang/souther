package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.values.AdmittedPlan;
import souther.compiler.values.Realizations;
import souther.compiler.values.Value;
import souther.compiler.values.ValueSet;

import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A position that published none of what its rules about the strings admit is one the reading gave
 * up on, or it is this check disagreeing with itself.
 *
 * <p>What the walks downstream do with such a position is nothing: the shortfall is the position's
 * and the position already carries it, so a second word from the walk would be one shortfall
 * reaching a reader twice. That silence is only right while the two really are the same position —
 * a position published nothing about whose own answer was built is one nothing says anything about,
 * and the silence would be the whole of what a reader was told.
 *
 * <p>So it is refused where the publishing happens. Nothing in this compiler produces that state
 * today: a set the answer needs is built while the answer is worked out, so a group that cannot be
 * built belongs to a position that was given up on. What is written here is that assumption, made
 * to fail out loud on the day a reading starts dropping a set a rule named.
 *
 * <p>Asked of the publishing and not of a model, because a model cannot reach it. A fixture that
 * could would be the state existing, which is the thing being denied.
 */
class WhatAPositionPublishesAboutItsStringsIsAnsweredOrRefusedTest {

    private static final Term.Interner NAMES = new Term.Interner();

    private static final FactSubject HERE = FactSubject.of(NAMES.written("some position"));

    private static final AdmittedPlan A_PLAN = AdmittedPlan.of(ValueSet.just(Value.text("x")));

    @Test
    void everySetItsRulesNameIsWhatAPositionPublishes() {
        assertInstanceOf(StringPublication.Complete.class,
                StatedByClauses.publicationOf(HERE,
                        new Realizations.Exact(Map.of(A_PLAN, ValueSet.ANY)), Set.of()),
                "a position whose sets were made publishes them, whatever the answer did");
    }

    @Test
    void andAPositionTheReadingGaveUpOnPublishesNoneOfThem() {
        assertInstanceOf(StringPublication.Incomplete.class,
                StatedByClauses.publicationOf(HERE, new Realizations.NotBuilt(), Set.of(HERE)),
                "the position carries what it could not work out, and this says the strings are"
                        + " part of it rather than saying it a second time");
    }

    @Test
    void andOneThatPublishedNothingWhileItsAnswerWasBuiltIsRefused() {
        assertThrows(AStringPublicationNothingAccountsFor.class,
                () -> StatedByClauses.publicationOf(HERE, new Realizations.NotBuilt(), Set.of()),
                "a position nothing was given up on and nothing was published about is a state this"
                        + " compiler has no account for, and going quiet about it would be the"
                        + " account");
    }
}
