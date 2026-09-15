package souther.compiler.meta;

import souther.compiler.ast.Hir;
import souther.compiler.diag.SourcePos;

import org.junit.jupiter.api.Test;

import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Whether a value's own equality is this comparison is answered off the parts it hands over, so
 * nothing it keeps out of them may reach a place this comparison answers differently.
 *
 * <p>Two halves, and the second is the one that can go wrong quietly. A value that hands its parts
 * over hands over all of them: {@link StructuralParts} reads every field a form declares and refuses
 * one it cannot read, so there is nothing kept back for an equality to read and this walk to miss. A
 * value that hands nothing over is answered without being looked inside at all — it is a written
 * value, held by what it says — and that answer is right only while what it holds is nothing this
 * comparison reads its own way.
 *
 * <p>The failure this catches has no symptom of its own. A value that kept where it was written,
 * behind an equality that read it, would be called safe to hold in a set, and the set would report
 * two builds as disagreeing over a line number. Nothing would say so, because nothing reaches the
 * refusal in the first place.
 */
class WhatAValueKeepsOutOfItsPartsIsNotReadDifferentlyHereTest {

    /** What the comparison is handed. Everything it reaches, it reaches from one of these. */
    private static final List<Class<?>> ROOTS = List.of(
            Hir.Data.class, Hir.SumData.class, Hir.UnitData.class,
            Hir.SpecBehavior.class, Hir.PipeBehavior.class, Hir.FnDef.class);

    /**
     * Every value a declaration reaches that this walk stops at holds nothing it answers differently
     * about.
     */
    @Test
    void nothingAStoppedWalkHoldsIsReadDifferentlyHere() {
        Set<Class<?>> stoppedAt = whereTheWalkStops();

        assertFalse(stoppedAt.isEmpty(),
                "a walk that stops nowhere would pass by reaching nothing to be wrong about");
        assertEquals(List.of(), new ArrayList<>(new TreeSet<>(stoppedAt.stream()
                        .filter(DeclarationAgreement::comparedTheSameByItsOwnEquality)
                        .filter(WhatAValueKeepsOutOfItsPartsIsNotReadDifferentlyHereTest::hides)
                        .map(Class::getName).toList())),
                "each of these is held by its own equality wherever a collection holds one, and"
                        + " keeps something this comparison reads its own way. What it keeps is read"
                        + " by that equality and by nothing here");
    }

    /**
     * The control: the sweep can tell a value that keeps such a thing from one that does not.
     *
     * <p>Without it the sweep above passes by finding nothing whether or not there is anything to
     * find, which is the shape of failure it exists to catch.
     */
    @Test
    void andAValueThatKeptOneWouldBeFound() {
        assertTrue(hides(KeepsWhereItWasWritten.class),
                "a value keeping where it was written keeps something this passes over");
        assertFalse(hides(KeepsAWord.class),
                "and one keeping a word keeps what this reads the same way");
    }

    /**
     * The other half: a form that hands its parts over hands over every one it has, so there is
     * nothing behind the parts for an equality to read.
     */
    @Test
    void andAFormThatHandsItsPartsOverKeepsNothingBehindThem() {
        for (Class<?> form : whereTheWalkGoesThrough()) {
            Set<String> handedOver = new LinkedHashSet<>();
            for (StructuralParts.Part part : StructuralParts.of(form)) {
                handedOver.add(part.name());
            }
            for (Field kept : form.getDeclaredFields()) {
                if (Modifier.isStatic(kept.getModifiers()) || kept.isSynthetic()) {
                    continue;
                }
                assertTrue(handedOver.contains(kept.getName()),
                        form.getName() + " keeps `" + kept.getName() + "` and hands it to nobody,"
                                + " so an equality of it reads what this cannot");
            }
        }
    }

    /** Stands for a value that keeps where it was written behind an equality that reads it. */
    private static final class KeepsWhereItWasWritten {

        @SuppressWarnings("unused")
        private final SourcePos at = new SourcePos(1, 1);
    }

    /** And one that keeps what this comparison reads the same way. */
    private static final class KeepsAWord {

        @SuppressWarnings("unused")
        private final String word = "amount";
    }

    /** Whether {@code type} keeps anything this comparison answers differently about. */
    private static boolean hides(Class<?> type) {
        Set<Class<?>> seen = new LinkedHashSet<>();
        Deque<Class<?>> todo = new ArrayDeque<>(List.of(type));
        while (!todo.isEmpty()) {
            Class<?> kept = todo.removeFirst();
            if (!seen.add(kept) || kept.isPrimitive() || kept.isEnum()
                    || kept.getPackageName().startsWith("java.")) {
                continue;
            }
            if (kept != type && !DeclarationAgreement.comparedTheSameByItsOwnEquality(kept)) {
                return true;
            }
            for (Field field : kept.getDeclaredFields()) {
                if (Modifier.isStatic(field.getModifiers()) || field.isSynthetic()) {
                    continue;
                }
                todo.addAll(StructuralParts.held(field.getGenericType()));
            }
        }
        return false;
    }

    /** The values a declaration reaches that this walk does not go inside. */
    private static Set<Class<?>> whereTheWalkStops() {
        Set<Class<?>> stopped = new LinkedHashSet<>();
        walk(stopped, new LinkedHashSet<>());
        return stopped;
    }

    /** And the forms it does. */
    private static Set<Class<?>> whereTheWalkGoesThrough() {
        Set<Class<?>> through = new LinkedHashSet<>();
        walk(new LinkedHashSet<>(), through);
        return through;
    }

    private static void walk(Set<Class<?>> stopped, Set<Class<?>> through) {
        Set<Class<?>> seen = new LinkedHashSet<>();
        Deque<Class<?>> todo = new ArrayDeque<>(ROOTS);
        while (!todo.isEmpty()) {
            Class<?> type = todo.removeFirst();
            if (!seen.add(type) || type.isPrimitive()) {
                continue;
            }
            if (type.isSealed()) {
                todo.addAll(List.of(type.getPermittedSubclasses()));
                continue;
            }
            if (!StructuralParts.areHandedOver(type)) {
                stopped.add(type);
                continue;
            }
            through.add(type);
            for (StructuralParts.Part part : StructuralParts.of(type)) {
                todo.addAll(StructuralParts.held(part.held()));
            }
        }
    }
}
