package souther.compiler.check;

import souther.compiler.numeric.NumericDomain.Bounds;
import souther.compiler.numeric.NumericDomain.LinearForm;
import souther.compiler.numeric.NumericDomain.Rel;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;

import org.junit.jupiter.api.Test;

import java.lang.reflect.Constructor;
import java.lang.reflect.ParameterizedType;
import java.lang.reflect.RecordComponent;
import java.lang.reflect.Type;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.fail;

/**
 * Every value a recipe is read from is a value the reading reaches.
 *
 * <p>{@link Terms#reached} answers which atoms a form is about, which is not which atoms it names: a
 * recipe stands under a name, and what the recipe was read from is under that. {@link
 * StepInputFacts} is the reader that made this matter — it keeps only the places the step names, so
 * a place reached through a recipe and not through the form goes unbounded, and the walk over it
 * fails to prove what its declarations say.
 *
 * <p>Which forms those are is the recipe's own answer ({@link Derivation#formsRead}), so the walk
 * has one case and not one per kind of recipe. That is where the question belongs: what a recipe is
 * read from is part of what the recipe means, and a walk that worked it out from which components
 * happen to be forms would be answering it by a naming convention — and would miss the first
 * dependency that arrives inside something else, which is what a condition's constraint would be.
 *
 * <p>So there are two things to hold, and they are different. That the walk follows what it is told
 * is one, and it is a walk over one list. That what it is told is everything is the other, and
 * nothing about a hand-written list can say it — which is what the second test here is for.
 */
class WhatARecipeIsReadFromIsWhatAReadingReachesTest {

    private static final BindingOwner OWNER = new BindingOwner.OfValue("demo", "f");

    private int minted;

    /** A subject nothing else is, so that finding it in an answer is finding this form and no
     * other. */
    private FactSubject marker() {
        return AsPlaces.of(new BindingId(OWNER, ++minted));
    }

    /**
     * The walk follows what a recipe says it is read from, however deep the recipes stand.
     *
     * <p>Two levels, because one would be answered by a walk that read a recipe and stopped: the
     * places under a product standing in a choice's arm are as much what the choice is about as the
     * arm's own are.
     */
    @Test
    void aReadingReachesWhatTheRecipesUnderItAreReadFrom() {
        Terms terms = new Terms(Symbols.none(souther.compiler.DefaultStdlib.get()), souther.compiler.query.ReadAs.THE_COMPILATION_DOES);
        FactSubject left = marker();
        FactSubject right = marker();
        FactSubject product = marker();
        FactSubject other = marker();
        FactSubject choice = marker();
        terms.computedBy(product, new AtomKnowledge.Computation.Derived(
                new Derivation.Product(LinearForm.atom(left), LinearForm.atom(right))));
        terms.computedBy(choice, new AtomKnowledge.Computation.Derived(new Derivation.Chosen(List.of(
                new Derivation.Chosen.Arm(LinearForm.atom(product), List.of()),
                new Derivation.Chosen.Arm(LinearForm.atom(other), List.of())))));

        assertEquals(Set.of(choice, product, other, left, right),
                terms.reached(LinearForm.atom(choice)),
                "the arms, and what the recipes under the arms are read from");
    }

    /**
     * And a value only what decides an arm names is reached, though no arm answers it.
     *
     * <p>The dependency that arrives inside something else. What an arm's context settles is read
     * later and against a domain, but what that reading may reach is decided now: a value it needs
     * and this does not reach arrives with its guarantee already dropped by {@link StepInputFacts},
     * and the walk fails to prove what the declarations say with nothing saying why.
     *
     * <p>Beside the reflection test below and not covered by it. That one catches a form a recipe
     * holds and does not declare; this catches a form the producer never put in the recipe at all,
     * which is a hand-written list being wrong rather than incomplete.
     */
    @Test
    void aReadingReachesWhatDecidedAnArmAndNotOnlyWhatTheArmsAnswer() {
        Terms terms = new Terms(Symbols.none(souther.compiler.DefaultStdlib.get()), souther.compiler.query.ReadAs.THE_COMPILATION_DOES);
        FactSubject answered = marker();
        FactSubject askedAbout = marker();
        FactSubject choice = marker();
        terms.computedBy(choice, new AtomKnowledge.Computation.Derived(new Derivation.Chosen(List.of(
                new Derivation.Chosen.Arm(LinearForm.atom(answered),
                        List.of(new NumericConstraint(LinearForm.atom(askedAbout), Rel.GE))),
                new Derivation.Chosen.Arm(LinearForm.atom(answered), List.of())))));

        assertTrue(terms.reached(LinearForm.atom(choice)).contains(askedAbout),
                "no arm answers it and deciding between them reads it, which is what the arm's"
                        + " context will be read from");
    }

    /** And a name nothing was filed against reaches only itself, so the answer above is the
     * recipes' doing and not something every subject gets. */
    @Test
    void aFormOverANameNothingWasRecordedAgainstReachesOnlyItself() {
        Terms terms = new Terms(Symbols.none(souther.compiler.DefaultStdlib.get()), souther.compiler.query.ReadAs.THE_COMPILATION_DOES);
        FactSubject named = marker();

        assertEquals(Set.of(named), terms.reached(LinearForm.atom(named)),
                "nothing is filed against it, so there is nothing under it to reach");
    }

    /**
     * Two recipes reading the same forms and stating the same relations are not the same recipe
     * where the relations stand beside different arms.
     *
     * <p>What a recipe is read from and what makes two of them one are different questions, and the
     * first flattens what the second turns on. A choice whose first arm is held below nought and
     * whose second is not reads the same forms as one where the second is held and the first is
     * not, and states the same relation; read as two flat lists they are one recipe. Filed under one
     * atom the second would be passed over as the first already recorded, and what that atom lies
     * between would turn on which reading named it first.
     *
     * <p>Held against {@link Terms#recording}'s own answer rather than against a comparison written
     * here: what it does with two recipes it takes for one is pass the second over, and what it does
     * with two it can tell apart is refuse them both ({@link Terms.OneTermTwoDerivations}).
     */
    @Test
    void twoChoicesDifferingOnlyInWhichArmStatesTheRelationAreNotOneRecipe() {
        Terms terms = new Terms(Symbols.none(souther.compiler.DefaultStdlib.get()), souther.compiler.query.ReadAs.THE_COMPILATION_DOES);
        FactSubject answered = marker();
        FactSubject other = marker();
        FactSubject atom = marker();
        Derivation stated = new Derivation.Chosen(List.of(
                new Derivation.Chosen.Arm(LinearForm.atom(answered),
                        List.of(new NumericConstraint(LinearForm.atom(other), Rel.LT))),
                new Derivation.Chosen.Arm(LinearForm.atom(other), List.of())));
        Derivation moved = new Derivation.Chosen(List.of(
                new Derivation.Chosen.Arm(LinearForm.atom(answered), List.of()),
                new Derivation.Chosen.Arm(LinearForm.atom(other),
                        List.of(new NumericConstraint(LinearForm.atom(other), Rel.LT)))));

        Set<FactSubject> readFrom = new LinkedHashSet<>();
        stated.formsRead().forEach(f -> readFrom.addAll(f.coefs().keySet()));
        Set<FactSubject> alsoReadFrom = new LinkedHashSet<>();
        moved.formsRead().forEach(f -> alsoReadFrom.addAll(f.coefs().keySet()));
        assertEquals(readFrom, alsoReadFrom,
                "the two are read from the same places, which is why the flat list cannot tell"
                        + " them apart");

        assertFalse(stated.sameAs(moved, SAME_NUMBERS),
                "the relation holds where a different arm is the answer, so they are two recipes");
        assertTrue(stated.sameAs(stated, SAME_NUMBERS), "and a recipe is itself");
    }

    /** Numbers compared as {@link Terms} compares them, so this asks the question the check asks. */
    private static final Derivation.Same SAME_NUMBERS = new Derivation.Same() {

        @Override
        public boolean forms(LinearForm<FactSubject> a, LinearForm<FactSubject> b) {
            return a.equals(b);
        }

        @Override
        public boolean extents(Bounds a, Bounds b) {
            return a == b;
        }
    };

    /**
     * And what a recipe says it is read from is every form it holds.
     *
     * <p>The other half, and the one a list written by hand cannot give. {@link
     * Derivation#formsRead} is what the walk trusts, so a component added to a recipe and left out
     * of that answer is a dependency the walk never hears about — and every test above it goes on
     * passing. So each kind of recipe is built with a marker wherever a form can stand and asked
     * what it is read from.
     *
     * <p>A component this cannot build is a failure and not a skip. What such a component is decides
     * whether a form can stand inside it, which is exactly the question, so the day one is added
     * this stops and says so rather than passing over it.
     */
    @Test
    void whatARecipeSaysItIsReadFromIsEveryFormItHolds() {
        Class<?>[] kinds = Derivation.class.getPermittedSubclasses();
        assertTrue(kinds != null && kinds.length > 0, "Derivation is a sum and has arms");
        for (Class<?> kind : kinds) {
            Set<FactSubject> put = new LinkedHashSet<>();
            Derivation recipe = (Derivation) build(kind, put);

            Set<FactSubject> said = new LinkedHashSet<>();
            recipe.formsRead().forEach(f -> said.addAll(f.coefs().keySet()));

            assertEquals(put, said, kind.getSimpleName() + " holds a form it does not say it is read"
                    + " from, so `Terms.reached` will never walk it and the places under it go"
                    + " unbounded with nothing saying so");
        }
    }

    /** One value of {@code type}, with a fresh marker atom wherever a {@link LinearForm} stands.
     * Each marker is recorded in {@code put} as it is minted, so what was built and what is expected
     * back are one answer rather than two that have to agree. */
    private Object build(Class<?> type, Set<FactSubject> put) {
        if (type == LinearForm.class) {
            FactSubject atom = marker();
            put.add(atom);
            return LinearForm.atom(atom);
        }
        if (type == Bounds.class) {
            return new Bounds(null, null);   // a range, and no form stands in one
        }
        if (type.isEnum()) {
            return type.getEnumConstants()[0];   // one of a fixed set, and no form stands in one
        }
        if (type.isRecord()) {
            return record(type, put);
        }
        return fail(type + " stands in a recipe and this test cannot build one. What it is decides"
                + " whether a form can stand inside it: teach this test to build it, and if one can,"
                + " teach that recipe's formsRead() to answer with it.");
    }

    /** {@code type}'s canonical constructor, called with one value built for each component. */
    private Object record(Class<?> type, Set<FactSubject> put) {
        RecordComponent[] components = type.getRecordComponents();
        Class<?>[] types = new Class<?>[components.length];
        Object[] values = new Object[components.length];
        for (int i = 0; i < components.length; i++) {
            types[i] = components[i].getType();
            values[i] = components[i].getType() == List.class
                    ? List.of(build(elementOf(components[i]), put),
                            build(elementOf(components[i]), put))
                    : build(components[i].getType(), put);
        }
        try {
            Constructor<?> canonical = type.getDeclaredConstructor(types);
            canonical.setAccessible(true);
            return canonical.newInstance(values);
        } catch (ReflectiveOperationException e) {
            return fail("could not build a " + type.getSimpleName() + ": " + e);
        }
    }

    /** What a component's list holds. Two of them are built for every list, so a recipe that
     * answered with its first arm and stopped is one this catches. */
    private static Class<?> elementOf(RecordComponent component) {
        Type generic = component.getGenericType();
        if (!(generic instanceof ParameterizedType p)) {
            return fail(component + " is a raw list and this test cannot say what it holds");
        }
        Type held = p.getActualTypeArguments()[0];
        if (held instanceof ParameterizedType inner && inner.getRawType() instanceof Class<?> raw) {
            return raw;
        }
        if (held instanceof Class<?> raw) {
            return raw;
        }
        return fail(component + " is a list of something this test cannot name");
    }
}
