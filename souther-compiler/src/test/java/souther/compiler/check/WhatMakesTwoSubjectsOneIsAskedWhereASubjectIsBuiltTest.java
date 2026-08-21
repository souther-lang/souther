package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.Type;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
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
        Terms terms = new Terms(Symbols.none(), souther.compiler.check.ReadAs.THE_COMPILATION_DOES);
        BindingId n = binding(0);
        Denotations at = Denotations.none().location(n, AsPlaces.of(n), AsPlaces.term(n));

        FactSubject first = terms.subjectOf(new Core.Read("n", n, Type.INT, POS), at);
        FactSubject second = terms.subjectOf(new Core.Read("n", n, Type.INT, POS), at);

        assertNotNull(first, "a place is something to point at");
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
        Terms terms = new Terms(Symbols.none(), souther.compiler.check.ReadAs.THE_COMPILATION_DOES);
        Denotations at = Denotations.none();
        Core one = unnameable();
        Core other = unnameable();

        FactSubject first = terms.subjectOf(one, at);
        FactSubject second = terms.subjectOf(other, at);

        assertNotNull(first, "an evaluation can be pointed at even where it cannot be named");
        assertNotEquals(first, second, "two occurrences are two evaluations");
    }

    /**
     * A referentially transparent operation over one evaluation answers one subject.
     *
     * <p>The closure the whole separation is for. An evaluation gets a subject because it can be
     * pointed at; whether two writings of something built <em>over</em> it are one value is then the
     * operation's to decide, and {@code List.length} decides it the way every pure operation does —
     * same operation, same arguments, same value. If a subject could only be composed out of things
     * the term grammar already named, an answer would be nameable and everything built from it would
     * not, and a fact about {@code length(xs)} would be about nothing by the second reading of it.
     */
    @Test
    void onePureApplicationToOneEvaluationHasOneSubject() {
        Terms terms = new Terms(Symbols.none(), souther.compiler.check.ReadAs.THE_COMPILATION_DOES);
        Denotations at = Denotations.none();
        Core answer = unnameable();

        assertEquals(terms.subjectOf(length(answer), at), terms.subjectOf(length(answer), at),
                "one operation over one evaluation is one value, however often it is written");
    }

    /** And over two evaluations it is two, because the arguments are two values. The control for the
     * law above: equality there must come from the operation composing, not from everything being
     * lumped together. */
    @Test
    void onePureApplicationToTwoEvaluationsHasTwoSubjects() {
        Terms terms = new Terms(Symbols.none(), souther.compiler.check.ReadAs.THE_COMPILATION_DOES);
        Denotations at = Denotations.none();

        assertNotEquals(terms.subjectOf(length(unnameable()), at),
                terms.subjectOf(length(unnameable()), at),
                "two evaluations are two values, so the sizes of them are two values");
    }

    /**
     * A part of an evaluation composes the same way anything else reads a field.
     *
     * <p>Not a projection machinery of its own. A place has one and a term has one, and an evaluation
     * having a third would be three rules to keep saying the same thing — {@code E.rank} is the field
     * {@code rank} read off whatever {@code E} is, which is what reading a field means everywhere.
     */
    @Test
    void aFieldReadOffAnEvaluationComposesWithIt() {
        Terms terms = new Terms(Symbols.none(), souther.compiler.check.ReadAs.THE_COMPILATION_DOES);
        Denotations at = Denotations.none();
        Core answer = unnameable();

        assertEquals(terms.subjectOf(field(answer, "rank"), at),
                terms.subjectOf(field(answer, "rank"), at),
                "one field of one evaluation is one value");
        assertNotEquals(terms.subjectOf(field(answer, "rank"), at),
                terms.subjectOf(answer, at),
                "and it is not the evaluation it is read off");
    }

    /**
     * An evaluation that reaches outside the language has a subject, and every ask of it has its own.
     *
     * <p>The half that used to be missing. What such a behavior answers cannot be shared — two asks
     * are two answers — and the only way to give a value a name was to declare it shared, so it was
     * given none. Having none is what left a construction over it neither proved nor refuted nor
     * reported (#819).
     *
     * <p>Having one is not the same as anything being known of it, and nothing here says it is: what
     * a construction over such an answer comes out as is held at
     * {@code AHelperCallIsNameableWhetherOrNotItWasExpandedTest}, and it is still silence.
     */
    @Test
    void anAnswerFromOutsideTheLanguageHasASubjectAndEachAskHasItsOwn() {
        Terms terms = new Terms(Symbols.none(), souther.compiler.check.ReadAs.THE_COMPILATION_DOES);
        Denotations at = Denotations.none();

        assertNotNull(terms.subjectOf(unnameable(), at),
                "two asks are two answers, which is a reason to keep them apart, not to refuse "
                        + "both a name");
        assertNotEquals(terms.subjectOf(unnameable(), at), terms.subjectOf(unnameable(), at),
                "and each ask is its own");
    }

    /**
     * A size taken over a part of an evaluation composes with it, like anything else built over one.
     *
     * <p>Held because this is where a closure that only went one level deep would show: the size rule
     * keys a count over the container it is really the size of, and that container is here a field of
     * something the term grammar cannot name. Were the composition to stop at either step, one
     * writing of this in a guard and another in a clause would be two values, and the guard could
     * never discharge the clause.
     */
    @Test
    void aSizeOverAPartOfAnEvaluationComposesWithIt() {
        Terms terms = new Terms(Symbols.none(), souther.compiler.check.ReadAs.THE_COMPILATION_DOES);
        Denotations at = Denotations.none();
        Core answer = unnameable();

        assertEquals(terms.subjectOf(length(items(answer)), at),
                terms.subjectOf(length(items(answer)), at),
                "one count of one field of one evaluation is one value");
        assertNotEquals(terms.subjectOf(length(items(answer)), at),
                terms.subjectOf(length(items(unnameable())), at),
                "and over another evaluation it is another value");
    }

    private static Core items(Core of) {
        return new Core.FieldAccess(of, "items", Type.list(Type.INT), POS);
    }

    private static Core field(Core of, String name) {
        return new Core.FieldAccess(of, name, Type.INT, POS);
    }

    /** And the same occurrence asked twice is one subject, or a fact filed under the first ask would
     * be about nothing by the second. */
    @Test
    void oneOccurrenceAskedTwiceIsOneSubject() {
        Terms terms = new Terms(Symbols.none(), souther.compiler.check.ReadAs.THE_COMPILATION_DOES);
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
        Terms terms = new Terms(Symbols.none(), souther.compiler.check.ReadAs.THE_COMPILATION_DOES);
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
        Terms terms = new Terms(Symbols.none(), souther.compiler.check.ReadAs.THE_COMPILATION_DOES);
        Denotations at = Denotations.none();

        assertNotEquals(terms.subjectOf(unnameable(), at), terms.subjectOf(unnameable(), at),
                "nothing said these were one occurrence, so they are two");
    }

    /**
     * A build that answers exactly as many as its source, and that source, have one size subject.
     *
     * <p>This is the one place equivalence is strengthened by making {@link Terms#subjectOf} the only
     * authority: read through the old one, {@code length(reverse(ns))} and {@code length(ns)} were two
     * subjects. They are one value, and the table already says so — {@code Cardinality.SAME} is a
     * statement about how many the result has, not about what this check happens to be able to
     * follow, which is what makes it something identity may read.
     *
     * <p>Held as a unit rather than through a program, because no program tells the two apart today:
     * the caller of {@code reportableSite} reads only whether it answered, so which subject it
     * answered with reaches nothing yet. That is what makes this safe to unify now, and it is also why
     * the rule needs holding here — nothing downstream would notice it going away.
     */
    @Test
    void aSizeAndTheSizeOfWhatItWasBuiltFromAreOneSubject() {
        Terms terms = new Terms(Symbols.none(), souther.compiler.check.ReadAs.THE_COMPILATION_DOES);
        BindingId ns = binding(2);
        Denotations at = Denotations.none().location(ns, AsPlaces.of(ns), AsPlaces.term(ns));
        Core list = new Core.Read("ns", ns, Type.list(Type.INT), POS);

        FactSubject ofTheSource = terms.subjectOf(length(list), at);
        assertNotNull(ofTheSource, "a size is a value this names, or the two below are one nothing");
        assertEquals(ofTheSource, terms.subjectOf(length(reverse(list)), at),
                "`reverse` answers exactly as many, so the two sizes are the one value");
    }

    /** And an operation the same table says may answer fewer is not identified with its source. */
    @Test
    void aSizeOfABuildThatMayAnswerFewerIsItsOwnSubject() {
        Terms terms = new Terms(Symbols.none(), souther.compiler.check.ReadAs.THE_COMPILATION_DOES);
        BindingId ns = binding(3);
        Denotations at = Denotations.none().location(ns, AsPlaces.of(ns), AsPlaces.term(ns));
        Core list = new Core.Read("ns", ns, Type.list(Type.INT), POS);

        assertNotEquals(terms.subjectOf(length(list), at),
                terms.subjectOf(length(distinct(list)), at),
                "`distinct` may answer fewer, so its size is a value of its own");
    }

    /**
     * A part of an evaluation is a part of that evaluation, not an evaluation of its own.
     *
     * <p>A clause is written about the parts — an {@code ensures} states {@code value.rank}, not
     * {@code value} — so an answer that could be pointed at while nothing inside it could would be a
     * subject nothing is ever about. The same rule {@link Location} carries for a place, asked here of
     * an evaluation.
     */
    @Test
    void aFieldReadOffAnEvaluationIsAPartOfIt() {
        Terms terms = new Terms(Symbols.none(), souther.compiler.check.ReadAs.THE_COMPILATION_DOES);
        Denotations at = Denotations.none();
        Core answer = unnameable();

        FactSubject whole = terms.subjectOf(answer, at);
        FactSubject part = terms.subjectOf(
                new Core.FieldAccess(answer, "rank", Type.INT, POS), at);

        assertNotNull(part, "a part of an evaluation is something to point at");
        assertNotEquals(whole, part, "the answer and the field read off it are two values");
        assertEquals(part, terms.subjectOf(
                new Core.FieldAccess(answer, "rank", Type.INT, POS), at),
                "and one field of one evaluation is one value");
    }

    private static Core length(Core of) {
        return new Core.PreservedCall(new souther.compiler.types.ValueName.Stdlib("List", "length"),
                java.util.List.of(of), Type.INT, POS);
    }

    private static Core reverse(Core of) {
        return new Core.PreservedCall(new souther.compiler.types.ValueName.Stdlib("List", "reverse"),
                java.util.List.of(of), of.type(), POS);
    }

    private static Core distinct(Core of) {
        return new Core.PreservedCall(new souther.compiler.types.ValueName.Stdlib("List", "distinct"),
                java.util.List.of(of), of.type(), POS);
    }

    /** A value of a shape no term covers: applying whatever a binding holds, which may be a behavior
     * injected from outside. */
    private static Core unnameable() {
        return new Core.Apply(new Core.Read("f", binding(1), Type.INT, POS), java.util.List.of(),
                Type.list(Type.INT), POS);
    }
}
