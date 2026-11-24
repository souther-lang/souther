package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.BorderObligationPointAssessment;
import souther.compiler.types.AnApplicationOfAClosure;
import souther.compiler.types.ApplicationsReadOn;

import java.lang.reflect.GenericArrayType;
import java.lang.reflect.ParameterizedType;
import java.lang.reflect.RecordComponent;
import java.lang.reflect.Type;
import java.lang.reflect.WildcardType;
import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Nothing that tells two readings of a line apart holds which applications of a closure read the
 * line.
 *
 * <p>What a reading is, is asked of these values by everything that keeps one of two alike, files
 * one under what it is, or tells two apart — their equality is the answer. An account of which
 * applications read a line held in one of them would make two readings of one line two, and a
 * reader keeping one of two alike would drop the other's account. So the account is held beside
 * them, by what it is of ({@link LinesReadOn}, {@link ReadingsReadOn}), and none of them reaches it
 * through any of its components, however deep.
 */
class WhatTellsReadingsApartHoldsNoAccountOfWhatReadThemTest {

    /** What tells readings of a line apart, and lines from one another. */
    private static final List<Class<?>> IDENTITIES = List.of(Border.class, Border.DrawnAt.class,
            LineOrigin.class, BoundaryLine.class, BorderObligationPointAssessment.Reading.class,
            WhereAPartDecides.class, PlaceOfALine.class, Cutting.class, Cutting.Read.class,
            UndividedByARelation.class);

    /** What says which applications read a line. */
    private static final Set<Class<?>> ACCOUNTS = Set.of(ApplicationsReadOn.class,
            AnApplicationOfAClosure.class, AnApplicationOfAClosure.Made.class, LinesReadOn.class,
            ReadingsReadOn.class);

    @Test
    void noComponentOfWhatTellsReadingsApartReachesAnAccount() {
        Set<String> reached = new TreeSet<>();
        Set<Class<?>> walked = new HashSet<>();
        Deque<Class<?>> left = new ArrayDeque<>(IDENTITIES);
        while (!left.isEmpty()) {
            Class<?> each = left.pop();
            if (!walked.add(each) || !each.getName().startsWith("souther.")) {
                continue;
            }
            if (ACCOUNTS.contains(each)) {
                reached.add(each.getName());
                continue;
            }
            if (each.isSealed()) {
                left.addAll(List.of(each.getPermittedSubclasses()));
            }
            if (each.isRecord()) {
                for (RecordComponent component : each.getRecordComponents()) {
                    classesIn(component.getGenericType(), left);
                }
            }
        }
        assertTrue(walked.size() > IDENTITIES.size(), "the walk went into the components");
        assertEquals(Set.of(), reached,
                "an account of what read a line, reached from what tells readings apart");
    }

    private static void classesIn(Type type, Deque<Class<?>> out) {
        switch (type) {
            case Class<?> plain -> out.push(plain.isArray() ? plain.getComponentType() : plain);
            case ParameterizedType parameterized -> {
                classesIn(parameterized.getRawType(), out);
                for (Type argument : parameterized.getActualTypeArguments()) {
                    classesIn(argument, out);
                }
            }
            case WildcardType wildcard -> {
                for (Type bound : wildcard.getUpperBounds()) {
                    classesIn(bound, out);
                }
            }
            case GenericArrayType array -> classesIn(array.getGenericComponentType(), out);
            default -> { }
        }
    }
}
