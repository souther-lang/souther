package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.Type;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * Whether a value can be pointed at, and whether two writings of it are one value, are two questions.
 *
 * <p>They were one. A subject was a {@link Term}, whose equality is structural, so anything given a
 * subject was thereby declared shareable — and a value that could be named but not shared had nowhere
 * to be. What that cost is written in #819: a call to a {@code behavior} was given no subject at all,
 * because the only way to give it one would have claimed that two asks of it answer alike. A
 * construction built from such an answer was then not checked and not reported.
 *
 * <p>So the order is fixed here: a subject exists because there is something to point at, and two
 * subjects are one because the way they are built makes them one. Both answers are settled where the
 * subject is built ({@link Terms#subjectOf}), so a reader handed a subject has no second question to
 * ask — and no way to answer it differently from the reader beside it.
 */
class WhatMakesTwoSubjectsOneIsAskedWhereASubjectIsBuiltTest {

    private static final SourcePos POS = new SourcePos(1, 1);

    private static BindingId binding(int index) {
        return new BindingId(new BindingOwner.OfValue("demo", "f"), index);
    }

    /** A place is shareable, and two readings of it are one subject. That is what makes a guard on
     * one writing of a name a guard on the next. */
    @Test
    void twoWritingsOfAPlaceAreOneSubject() {
        Terms terms = new Terms(Symbols.none());
        BindingId n = binding(0);
        Denotations at = Denotations.none().location(n);

        FactSubject first = terms.subjectOf(new Core.Read("n", n, Type.INT, POS), at);
        FactSubject second = terms.subjectOf(new Core.Read("n", n, Type.INT, POS), at);

        assertInstanceOf(FactSubject.OfATerm.class, first, "a place is named by the way it is built");
        assertEquals(first, second, "so two writings of it are one subject");
    }

    /**
     * An evaluation the term grammar cannot name is one subject per occurrence.
     *
     * <p>Two of them written the same way are two subjects, which is the answer a value nothing may
     * share needs — what an injected behavior answers is a different value each time it is asked. It
     * is also the safe answer for a value that may be shared: two subjects say less than one, and
     * saying less is not saying something false.
     */
    @Test
    void twoOccurrencesOfAnUnnameableEvaluationAreTwoSubjects() {
        Terms terms = new Terms(Symbols.none());
        Denotations at = Denotations.none();
        Core one = unnameable();
        Core other = unnameable();

        FactSubject first = terms.subjectOf(one, at);
        FactSubject second = terms.subjectOf(other, at);

        assertNotNull(first, "an evaluation can be pointed at even where it cannot be named");
        assertInstanceOf(FactSubject.OfAnEvaluation.class, first,
                "and pointing at it is what it is given");
        assertNotEquals(first, second, "two occurrences are two evaluations");
    }

    /** And the same occurrence asked twice is one subject, or a fact filed under the first ask would
     * be about nothing by the second. */
    @Test
    void oneOccurrenceAskedTwiceIsOneSubject() {
        Terms terms = new Terms(Symbols.none());
        Denotations at = Denotations.none();
        Core once = unnameable();

        assertEquals(terms.subjectOf(once, at), terms.subjectOf(once, at),
                "an occurrence is asked about more than once, and it is one evaluation");
    }

    /**
     * Rewriting does not create an evaluation.
     *
     * <p>A reading that replaces a conditional rebuilds every node on the way to it, so the very same
     * call arrives as a different object in each reading. That is the check reconstructing a tree, not
     * the program evaluating anything twice, and an occurrence that came through one is the occurrence
     * it was built from.
     *
     * <p>Held as a law rather than left to the rewrite that happens to record it: what a fact is about
     * has to survive the analysis rearranging its own input, and a reading that gave one call two
     * evaluations would take a fact in under the first and read it back under the second — finding
     * nothing, and reporting a construction it had already settled.
     */
    @Test
    void rebuildingAnOccurrenceDoesNotMakeASecondEvaluation() {
        Terms terms = new Terms(Symbols.none());
        Denotations at = Denotations.none();
        Core written = unnameable();
        FactSubject before = terms.subjectOf(written, at);

        Core rebuilt = unnameable();          // the same expression, built again by a rewrite
        terms.rebuilt(rebuilt, written);

        assertEquals(before, terms.subjectOf(rebuilt, at),
                "a node a rewrite built is the occurrence it was built from");
    }

    /**
     * And the pair of it: a second evaluation is a second subject.
     *
     * <p>The two are told apart by where they come from rather than by what they look like. Something
     * a rewrite built is recorded as built from what it replaced; something the program evaluates
     * again was never recorded, so it keeps the fresh identity it was given. Deciding it by how the
     * two are written would be the mistake this whole model exists to avoid — two writings alike is
     * exactly what a shareable value and an unshareable one have in common.
     */
    @Test
    void anEvaluationNoRewriteAccountsForIsASecondEvaluation() {
        Terms terms = new Terms(Symbols.none());
        Denotations at = Denotations.none();

        assertNotEquals(terms.subjectOf(unnameable(), at), terms.subjectOf(unnameable(), at),
                "nothing said these were one occurrence, so they are two");
    }

    /** A value of a shape no term covers: applying whatever a binding holds, which may be a behavior
     * injected from outside. */
    private static Core unnameable() {
        return new Core.Apply(new Core.Read("f", binding(1), Type.INT, POS), java.util.List.of(),
                Type.INT, POS);
    }
}
