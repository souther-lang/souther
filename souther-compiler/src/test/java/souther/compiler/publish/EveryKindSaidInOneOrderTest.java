package souther.compiler.publish;

import org.junit.jupiter.api.Test;

import souther.compiler.observe.Incompleteness;
import souther.compiler.partition.ReadingGap;

import java.io.File;
import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.lang.reflect.RecordComponent;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.fail;

/**
 * What a report says a kind of reason in the order of, and that there is one such order per kind.
 *
 * <p>An order is a sequence, so repeats, pairs out of order and two members in one place are all
 * things a sequence cannot hold. What a sequence can be wrong about is holding fewer members than
 * the kind has — a reason nothing would ever publish — and about there being a second sequence over
 * the same kind somewhere else, which is the thing that puts two lines of one block in two orders.
 * Both are asked of every order there is rather than of the one somebody was editing.
 *
 * <p>The population is read off the declarations. What the kinds are is read off the types, and
 * which orders exist is read off the class files of the package that is allowed to declare them —
 * so an order added, or a member added to a kind, arrives here without anybody adding a line.
 */
class EveryKindSaidInOneOrderTest {

    /**
     * Every order holds every member of its kind, once each.
     *
     * <p>The one property a written sequence cannot carry for itself. A member the order leaves out
     * is one a report could be owed and no order anywhere would place — the widening would be made,
     * every other test would go on passing, and the sentence would quietly answer a narrower
     * question than the type does.
     */
    @Test
    void everyOrderHoldsEveryMemberOfItsKind() throws Exception {
        for (Map.Entry<String, CanonicalSelection.Order<?>> each : declaredOrders().entrySet()) {
            List<Object> slots = each.getValue().slots();
            assertEquals(universeOf(slots), new LinkedHashSet<>(slots),
                    () -> each.getKey() + " does not say every member of its kind, or says one"
                            + " nothing else does");
            assertEquals(slots.size(), Set.copyOf(slots).size(),
                    () -> each.getKey() + " says a member twice");
        }
    }

    /**
     * One kind, one order.
     *
     * <p>What the whole of this is for. A kind said in two places — an observation's code is said of
     * a reading that stopped short and again of a value nothing could read back — put in order twice
     * would put the same pair of reasons in two orders on two lines of one block, and nothing in
     * either line would say which was meant.
     */
    @Test
    void noKindIsPutInOrderTwice() throws Exception {
        Map<Class<?>, String> byKind = new LinkedHashMap<>();
        for (Map.Entry<String, CanonicalSelection.Order<?>> each : declaredOrders().entrySet()) {
            Class<?> kind = kindOf(each.getValue().slots());
            String already = byKind.put(kind, each.getKey());
            assertEquals(null, already,
                    () -> kind.getSimpleName() + " is put in order by " + already + " and by "
                            + each.getKey() + ", and the two are free to differ");
        }
    }

    /**
     * A kind written out of another kind's order carries that order and does not restate it.
     *
     * <p>The reading gaps are the observation codes with the one reason that is no observation's
     * after them. Written again rather than composed, the two would be two orders over the codes
     * that agree until somebody moves one of them.
     */
    @Test
    void theReadingGapsAreTheObservationCodesAndNotASecondOrderOverThem() {
        List<Object> codesInReadingOrder = new ArrayList<>();
        for (Object gap : PublicationOrders.READING_GAPS.slots()) {
            if (gap instanceof ReadingGap.Observation it) {
                codesInReadingOrder.add(it.code());
            }
        }

        assertEquals(PublicationOrders.OBSERVATION_CODES.slots(), codesInReadingOrder,
                "a reading that met an observation's code is that code, and there is one order"
                        + " over the codes");
    }

    /**
     * What comes out of an order is that order with what was not held left out.
     *
     * <p>Said of the mechanism rather than of a value it made, and of every order at once. The
     * order the members arrived in is the walk's, so a selection that kept any of it would be a
     * report a reader cannot compare with the last run.
     */
    @Test
    void whatIsKeptIsTheOrderItselfWithWhatIsHeldLeftIn() throws Exception {
        for (Map.Entry<String, CanonicalSelection.Order<?>> each : declaredOrders().entrySet()) {
            List<Object> slots = each.getValue().slots();
            if (slots.getFirst() instanceof Class<?>) {
                // An order over arms places values this cannot make: what a member of one holds is
                // the arm's, and building one here would be this test deciding it.
                continue;
            }
            @SuppressWarnings("unchecked")
            CanonicalSelection.Order<Object> order =
                    (CanonicalSelection.Order<Object>) each.getValue();

            assertEquals(slots, order.keep(slots).written(),
                    () -> each.getKey() + " does not keep everything it holds");
            assertEquals(slots, order.keep(slots.reversed()).written(),
                    () -> each.getKey() + " kept the order they arrived in");
            assertEquals(List.of(), order.keep(List.of()).written(),
                    () -> each.getKey() + " made something of nothing being held");
            assertEquals(List.of(slots.getLast()), order.keep(List.of(slots.getLast())).written(),
                    () -> each.getKey() + " does not keep one of them on its own");
        }
    }

    /**
     * A member with no place in the order is refused rather than dropped.
     *
     * <p>Dropped, it would be a reason something is open that no report anywhere says. What is
     * handed over is what was met, and an order that cannot place one of them is the order being
     * wrong rather than the reason.
     */
    @Test
    void aMemberWithNoPlaceInTheOrderIsRefused() {
        @SuppressWarnings("unchecked")
        CanonicalSelection.Order<Object> codes =
                (CanonicalSelection.Order<Object>) (CanonicalSelection.Order<?>)
                        PublicationOrders.OBSERVATION_CODES;

        assertThrows(IllegalArgumentException.class,
                () -> codes.keep(List.of(ReadingGap.NO_VALUE)),
                "a member of another kind has no place here, and saying so is the answer");
    }

    /**
     * Two members in one place are refused, and one member arriving twice is one member.
     *
     * <p>The two are not the same thing. A reason met at seven readings is one reason, and a place
     * with room for one that two different things want is an order that cannot say what happened.
     */
    @Test
    void twoMembersInOnePlaceAreRefusedAndOneMetTwiceIsOne() {
        assertEquals(List.of(Incompleteness.Code.VALUE_TRUNCATED),
                PublicationOrders.OBSERVATION_CODES.keep(List.of(
                        Incompleteness.Code.VALUE_TRUNCATED,
                        Incompleteness.Code.VALUE_TRUNCATED)).written(),
                "one reason met twice is one reason");
        assertThrows(IllegalArgumentException.class,
                () -> PublicationOrders.ESTABLISHMENT_GAPS.keep(List.of(
                        souther.compiler.query.EstablishmentGap.Observation.of(
                                List.of(Incompleteness.Code.VALUE_TRUNCATED)),
                        souther.compiler.query.EstablishmentGap.Observation.of(
                                List.of(Incompleteness.Code.VALUE_UNREADABLE)))),
                "two observations are one observation naming both, and putting them in order is"
                        + " not what makes them one");
    }

    /**
     * Nothing but {@link PublicationOrders} declares one.
     *
     * <p>Making an order is closed to the package by the compiler, which leaves one way for a
     * second order over a kind to be written: another class in this package. What the check above
     * would say of such a class is nothing, because it reads the orders off this one.
     */
    @Test
    void nothingElseInThisPackageDeclaresAnOrder() throws Exception {
        for (Class<?> each : classesInThisPackage()) {
            if (each.equals(PublicationOrders.class)) {
                continue;
            }
            for (Field field : each.getDeclaredFields()) {
                assertNotEquals(CanonicalSelection.Order.class, field.getType(),
                        () -> each.getSimpleName() + " declares an order, and the orders are"
                                + " written in one place so that a kind cannot have two");
            }
        }
    }

    /** Every order this compiler publishes anything in, by the name it is declared under. */
    private static Map<String, CanonicalSelection.Order<?>> declaredOrders() throws Exception {
        Map<String, CanonicalSelection.Order<?>> out = new LinkedHashMap<>();
        for (Field each : PublicationOrders.class.getDeclaredFields()) {
            if (each.getType().equals(CanonicalSelection.Order.class)
                    && Modifier.isStatic(each.getModifiers())) {
                each.setAccessible(true);
                out.put(each.getName(), (CanonicalSelection.Order<?>) each.get(null));
            }
        }
        assertTrue(out.size() > 1, "the orders are read off the declarations, and this found none");
        return out;
    }

    /** What kind an order is over, read off what it places. */
    private static Class<?> kindOf(List<Object> slots) {
        Object first = slots.getFirst();
        if (first instanceof Class<?> arm) {
            return sealedOver(arm);
        }
        if (first instanceof Enum<?> constant) {
            return constant.getDeclaringClass();
        }
        return sealedOver(first.getClass());
    }

    /** Every member the kind of {@code slots} has. */
    private static Set<Object> universeOf(List<Object> slots) throws Exception {
        Object first = slots.getFirst();
        if (first instanceof Class<?> arm) {
            return new LinkedHashSet<>(List.of(sealedOver(arm).getPermittedSubclasses()));
        }
        if (first instanceof Enum<?> constant) {
            return new LinkedHashSet<>(List.of(constant.getDeclaringClass().getEnumConstants()));
        }
        Set<Object> out = new LinkedHashSet<>();
        for (Class<?> arm : sealedOver(first.getClass()).getPermittedSubclasses()) {
            out.addAll(valuesOf(arm));
        }
        return out;
    }

    /**
     * Every value one arm of a sum has.
     *
     * <p>Read off the arm rather than written down beside it. An arm this cannot enumerate says so
     * — the check is then one nobody can rely on, and a reader is told which arm to say how to
     * count rather than left with a test that quietly stopped covering it.
     */
    private static List<Object> valuesOf(Class<?> arm) throws Exception {
        RecordComponent[] held = arm.getRecordComponents();
        if (held == null) {
            return fail(arm.getSimpleName() + " is not a record, and this does not know what values"
                    + " it has: say here how they are counted");
        }
        if (held.length == 0) {
            return List.of(arm.getDeclaredConstructor().newInstance());
        }
        if (held.length == 1 && held[0].getType().isEnum()) {
            List<Object> out = new ArrayList<>();
            for (Object constant : held[0].getType().getEnumConstants()) {
                out.add(arm.getDeclaredConstructor(held[0].getType()).newInstance(constant));
            }
            return out;
        }
        return fail(arm.getSimpleName() + " holds more than a name of something finite, so the"
                + " values it has are not something this can count: say here how they are");
    }

    /** The sum {@code arm} is one of. */
    private static Class<?> sealedOver(Class<?> arm) {
        for (Class<?> each : arm.getInterfaces()) {
            if (each.isSealed()) {
                return each;
            }
        }
        return fail(arm.getSimpleName() + " is placed by an order and is no arm of a sum, so what"
                + " the kind is cannot be read off it");
    }

    /** Every class of this package, read off what was compiled. */
    private static List<Class<?>> classesInThisPackage() throws Exception {
        Path root = Path.of(CanonicalSelection.class.getProtectionDomain()
                .getCodeSource().getLocation().toURI());
        Path here = root.resolve(CanonicalSelection.class.getPackageName().replace('.', '/'));
        List<Class<?>> out = new ArrayList<>();
        try (Stream<Path> files = Files.walk(here)) {
            for (Path each : files.filter(p -> p.toString().endsWith(".class")).toList()) {
                out.add(Class.forName(root.relativize(each).toString()
                        .replace(File.separatorChar, '.').replaceFirst("\\.class$", ""),
                        false, CanonicalSelection.class.getClassLoader()));
            }
        }
        assertTrue(out.contains(PublicationOrders.class),
                "the classes of this package are read off what was compiled, and this found none");
        return out;
    }
}
