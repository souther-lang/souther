package souther.compiler.check;

import souther.compiler.DefaultStdlib;
import souther.compiler.ast.Hir;
import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.query.ReadAs;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.Type;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * Entering one binding under two environments answers once for each of them, not once for the
 * first to ask.
 *
 * <p>{@link Terms#inside} holds what a {@code let} answers against the binding <em>and</em> the
 * environment it was read in, because the same source text of a binding means something different
 * under two environments — {@code let y = x in y} names whatever {@code x} was under the one it is
 * read in. A cache keyed by the binding alone would answer the second environment with the first's
 * name for {@code x}, which is a name for the wrong value.
 *
 * <p>This is the safety condition the memoization rests on and not a claim {@link Terms#inside}
 * makes about the values themselves, so it is asked of one binding read under two hand-built
 * environments rather than of a chain deep enough to make the difference show up as a wrong answer
 * about arithmetic.
 */
class ACachedBindingAnswersForTheEnvironmentItWasEnteredInTest {

    private static final SourcePos POS = new SourcePos(0, 0);
    private static final BindingOwner OWNER = new BindingOwner.OfValue("demo", "f");

    @Test
    void theSameLetInAnswersDifferentlyUnderTwoEnvironments() {
        Hir.Binders binders = new Hir.Binders(OWNER);
        Core.Binder xBinder = CoreBinders.of(binders.binder("x", POS));
        Core.Binder yBinder = CoreBinders.of(binders.binder("y", POS));
        // Two bindings the test alone introduces, whose only use is to mint two subjects that are
        // not equal to each other — what x is named in each environment, and nothing more.
        Core.Binder markerA = CoreBinders.of(binders.binder("markerA", POS));
        Core.Binder markerB = CoreBinders.of(binders.binder("markerB", POS));

        Core.LetIn li = new Core.LetIn(yBinder,
                new Core.Read("x", xBinder.binding(), Type.INT, POS),
                new Core.Read("y", yBinder.binding(), Type.INT, POS), Type.INT, POS);

        Terms terms = new Terms(Terms.Of.THE_DISCHARGE_TREE, RuleReadingContext.unshared(
                RuleReadings.ofNoClauseFiled(Symbols.none(DefaultStdlib.get())),
                ReadAs.THE_COMPILATION_DOES));
        FactSubject subjectA = terms.placeSubject(markerA.binding());
        FactSubject subjectB = terms.placeSubject(markerB.binding());
        Denotations at1 = Denotations.none()
                .location(xBinder.binding(), subjectA, terms.placeTerm(markerA.binding()));
        Denotations at2 = Denotations.none()
                .location(xBinder.binding(), subjectB, terms.placeTerm(markerB.binding()));

        // The same LetIn object, read under each environment in turn — a cache that dropped the
        // environment from its key would answer the second ask with the first environment's y.
        Denotations under1 = terms.inside(li, at1);
        Denotations under2 = terms.inside(li, at2);

        assertEquals(subjectA, under1.subject(yBinder.binding()), "y under the environment naming x as A");
        assertEquals(subjectB, under2.subject(yBinder.binding()), "y under the environment naming x as B");
        assertNotEquals(under1.subject(yBinder.binding()), under2.subject(yBinder.binding()));
    }
}
