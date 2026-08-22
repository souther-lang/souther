package souther.compiler.check;

import souther.compiler.numeric.NumericDomain.Bounds;
import souther.compiler.numeric.NumericDomain.LinearForm;
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
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.fail;

/**
 * Every value a recipe is read from is a value the reading reaches.
 *
 * <p>{@link Terms#reached} answers which atoms a form is about, which is not which atoms it names: a
 * recipe stands under a name, and what the recipe was computed from is under that. {@link
 * StepInputFacts} is the reader that made this matter — it keeps only the places the step names, so
 * a place reached through a recipe and not through the form goes unbounded, and the walk over it
 * fails to prove what its declarations say.
 *
 * <p>Held against the recipes themselves rather than against a list written here. A recipe is a
 * record and what it is read from are its own components, so this builds one of each with a marker
 * in every place a form can stand and asks whether the reading found them. A component this cannot
 * build is a failure and not a skip: what such a component is, is a value the recipe holds, and
 * whether the reading follows it is exactly the question — so the day one is added, this stops and
 * says so rather than passing over it.
 *
 * <p>The condition an arm was chosen under is where this is going to be asked next. It is not part
 * of a recipe today ({@link Derivation.Chosen}), and it carries forms about the very places a step
 * reads — so a reading that followed the arms and not the conditions would bound a walk by half of
 * what it was told. That is this test's subject and not a remark about it: adding the field is what
 * makes this fail.
 */
class WhatARecipeIsReadFromIsWhatAReadingReachesTest {

    private static final BindingOwner OWNER = new BindingOwner.OfValue("demo", "f");

    private int minted;

    /** A subject nothing else is, so that finding it in the answer is finding this form and no
     * other. */
    private FactSubject marker() {
        return AsPlaces.of(new BindingId(OWNER, ++minted));
    }

    /**
     * Every kind of recipe there is, built with a marker wherever a form can stand, and read back
     * through {@link Terms#reached}.
     *
     * <p>One test over the sum and not one per arm: what is being held is that the reading follows a
     * recipe's forms, and which recipes there are is the sum's own answer. An arm added without a
     * case here is an arm this asks about all the same.
     */
    @Test
    void everyFormARecipeHoldsIsReachedThroughIt() {
        Class<?>[] kinds = Derivation.class.getPermittedSubclasses();
        assertTrue(kinds != null && kinds.length > 0, "Derivation is a sum and has arms");
        for (Class<?> kind : kinds) {
            Terms terms = new Terms(Symbols.none(),
                    souther.compiler.query.ReadAs.THE_COMPILATION_DOES);
            Set<FactSubject> put = new LinkedHashSet<>();
            Derivation recipe = (Derivation) build(kind, put);
            FactSubject named = marker();
            terms.derivations().put(named, recipe);

            Set<FactSubject> reached = terms.reached(LinearForm.atom(named));

            Set<FactSubject> want = new LinkedHashSet<>(put);
            want.add(named);
            assertEquals(want, reached, kind.getSimpleName() + " is read from every form it holds,"
                    + " so a reading of it reaches every atom those name");
        }
    }

    /** And the marker really is invisible without the recipe, so the answer above is the recipe's
     * doing and not something every subject gets. */
    @Test
    void aFormOverANameNothingWasRecordedAgainstReachesOnlyItself() {
        Terms terms = new Terms(Symbols.none(),
                souther.compiler.query.ReadAs.THE_COMPILATION_DOES);
        FactSubject named = marker();

        assertEquals(Set.of(named), terms.reached(LinearForm.atom(named)),
                "nothing is filed against it, so there is nothing under it to reach");
    }

    /**
     * One value of {@code type}, with a fresh marker atom wherever a {@link LinearForm} stands.
     *
     * <p>Each marker is recorded in {@code put} as it is minted, so what this built and what is
     * expected back are one answer rather than two that have to agree.
     */
    private Object build(Class<?> type, Set<FactSubject> put) {
        if (type == LinearForm.class) {
            FactSubject atom = marker();
            put.add(atom);
            return LinearForm.atom(atom);
        }
        if (type == Bounds.class) {
            return new Bounds(null, null);   // a range, and no form stands in one
        }
        if (type.isRecord()) {
            return record(type, put);
        }
        return fail(type + " stands in a recipe and this test cannot build one. What it is decides"
                + " whether Terms.reached has to follow it: teach this test to build it, and if a"
                + " form can stand anywhere inside it, teach `reached` to walk it.");
    }

    /** {@code type}'s canonical constructor, called with one value built for each component. */
    private Object record(Class<?> type, Set<FactSubject> put) {
        RecordComponent[] components = type.getRecordComponents();
        Class<?>[] types = new Class<?>[components.length];
        Object[] values = new Object[components.length];
        for (int i = 0; i < components.length; i++) {
            types[i] = components[i].getType();
            values[i] = components[i].getType() == List.class
                    ? List.of(build(elementOf(components[i]), put), build(elementOf(components[i]), put))
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

    /** What a component's list holds. Two of them are built for every list, so a reading that
     * followed the first arm and stopped is one this catches. */
    private static Class<?> elementOf(RecordComponent component) {
        Type generic = component.getGenericType();
        if (generic instanceof ParameterizedType p
                && p.getActualTypeArguments()[0] instanceof ParameterizedType inner
                && inner.getRawType() instanceof Class<?> raw) {
            return raw;
        }
        if (generic instanceof ParameterizedType p
                && p.getActualTypeArguments()[0] instanceof Class<?> raw) {
            return raw;
        }
        return fail(component + " is a list of something this test cannot name");
    }
}
