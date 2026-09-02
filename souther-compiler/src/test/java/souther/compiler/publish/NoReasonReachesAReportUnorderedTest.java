package souther.compiler.publish;

import org.junit.jupiter.api.Test;

import souther.compiler.query.EstablishmentGap;
import souther.compiler.query.ObligationDisposition;
import souther.compiler.report.AdequacyReport;

import java.io.File;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.lang.reflect.ParameterizedType;
import java.lang.reflect.RecordComponent;
import java.lang.reflect.Type;
import java.lang.reflect.WildcardType;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Nothing a report is handed carries a kind of reason without the order it is said in.
 *
 * <p>What the orders themselves cannot say. A kind is put in order in one place and there is one
 * way to select from it — and a plurality that reaches a report as a bare set has gone round both,
 * leaving the report to take an order from whatever the set iterates in.
 *
 * <p><b>Which kinds, read from the report's side and not from the orders.</b> Every enum of this
 * compiler is one, whether or not anybody has written an order for it: an enum is a universe fixed
 * by a declaration, so a set of one iterates in the order the constants were written, and a set
 * that reaches a report is one a sentence can be built from. Read from the orders instead, the
 * check would say that the kinds somebody has already put in order are in order — an enum added
 * with no order would be outside the question rather than the answer to it.
 *
 * <p>Beside those, the kinds that do have an order, which are sums as well as enums. What is not
 * here is a sum of this compiler's whose members name things in the model a person wrote — the
 * cases of a type, the terms of a quantity. Those are as many as the model has and their order is
 * the model's or the alphabet's, which is an order somebody decided.
 *
 * <p>Two ways in, because a report is handed things two ways. It reads what values hold and what
 * they answer, and it hands pluralities to its own writers as arguments — which is the shape the
 * defect had: a private method taking the budgets as a set and joining them.
 */
class NoReasonReachesAReportUnorderedTest {

    /**
     * Nothing a report can reach holds a kind of reason as a set.
     *
     * <p>Walked rather than listed: from everything that writes a report, through what its values
     * hold and what they answer, into every arm of every sum on the way. A value added between the
     * two arrives here without anybody adding a line.
     *
     * <p>A set and not any collection. A list was put in an order by whoever built it — the modules
     * of a compilation are answered in the order their sources were given — and a set was not, so a
     * set is where an order gets invented at the far end.
     */
    @Test
    void nothingAReportReachesHoldsAKindAsASet() throws Exception {
        List<String> found = new ArrayList<>();
        Set<Class<?>> seen = new LinkedHashSet<>();
        Deque<Class<?>> left = new ArrayDeque<>(everyReport());
        while (!left.isEmpty()) {
            Class<?> here = left.removeFirst();
            if (!seen.add(here)) {
                continue;
            }
            for (Class<?> arm : here.isSealed() ? here.getPermittedSubclasses() : new Class<?>[0]) {
                left.addLast(arm);
            }
            for (Member each : membersOf(here)) {
                if (each.type() instanceof ParameterizedType held
                        && Set.class.isAssignableFrom(rawOf(held.getRawType()))
                        && isAKind(rawOf(held.getActualTypeArguments()[0]))) {
                    found.add(here.getSimpleName() + "." + each.name() + " holds "
                            + rawOf(held.getActualTypeArguments()[0]).getSimpleName()
                            + " as a set, so what a report says them in is what it iterates in");
                }
                for (Class<?> reached : typesIn(each.type())) {
                    if (reached.getPackageName().startsWith("souther.compiler")) {
                        left.addLast(reached);
                    }
                }
            }
        }

        // The walk reaches what this is about, said out loud. A walk that stopped early would find
        // nothing to name and pass for the reason a clean one does.
        assertTrue(seen.contains(EstablishmentGap.Observation.class)
                        && seen.contains(ObligationDisposition.Undecided.class),
                () -> "the walk does not reach the values this is about, so what it found is not"
                        + " what a report can be handed: " + seen.size() + " types reached");
        assertEquals(List.of(), found,
                "a report can reach a kind of reason with no order on it");
    }

    /**
     * Nothing a report writes takes or answers with an unordered plurality of a kind.
     *
     * <p>The shape the defect had, and the one the walk above cannot see: what a report hands its
     * own writers. A method taking the budgets as a set joined them in whatever the set iterated
     * in, and no type anywhere held that.
     *
     * <p>A set or a bare collection, and not a list. A list was put in an order by whoever built it
     * and some of those orders are the author's — the reasons a question stands are said in the
     * order the clauses were written, and sorting them would answer by a precedence nothing in the
     * model decides. What a set or a {@code Collection} says is that whoever built it decided
     * nothing, which is the plurality this is about.
     *
     * <p>Read off every method a report declares, private ones included. What a document says is
     * built by the ones nobody outside calls.
     */
    @Test
    void nothingAReportWritesTakesOrAnswersWithAnUnorderedPluralityOfAKind() throws Exception {
        List<String> found = new ArrayList<>();
        for (Class<?> each : everyReport()) {
            for (Method method : each.getDeclaredMethods()) {
                List<Type> said = new ArrayList<>(List.of(method.getGenericParameterTypes()));
                said.add(method.getGenericReturnType());
                for (Type type : said) {
                    if (type instanceof ParameterizedType held
                            && unordered(rawOf(held.getRawType()))
                            && isAKind(rawOf(held.getActualTypeArguments()[0]))) {
                        found.add(each.getSimpleName() + "." + method.getName() + " takes or"
                                + " answers with an unordered plurality of "
                                + rawOf(held.getActualTypeArguments()[0]).getSimpleName());
                    }
                }
            }
        }

        assertEquals(List.of(), found,
                "a report writer is handed a plurality of a kind of reason that nobody put in an"
                        + " order, and what it says them in is then what that happens to iterate in");
    }

    /** Whether a plurality of this shape arrives with nobody having decided its order. */
    private static boolean unordered(Class<?> held) {
        return Set.class.isAssignableFrom(held)
                || held.equals(Collection.class) || held.equals(Iterable.class);
    }

    /**
     * Everything that writes a report, read off what was compiled.
     *
     * <p>The package and not the one class in it that writes the block this began with. A second
     * writer added beside it is a second place a plurality can be handed to, and the walk finds it
     * without anybody adding a line here.
     */
    private static List<Class<?>> everyReport() throws Exception {
        Path root = Path.of(AdequacyReport.class.getProtectionDomain()
                .getCodeSource().getLocation().toURI());
        Path here = root.resolve(AdequacyReport.class.getPackageName().replace('.', '/'));
        List<Class<?>> out = new ArrayList<>();
        try (Stream<Path> files = Files.walk(here)) {
            for (Path each : files.filter(p -> p.toString().endsWith(".class")).toList()) {
                out.add(Class.forName(root.relativize(each).toString()
                        .replace(File.separatorChar, '.').replaceFirst("\\.class$", ""),
                        false, AdequacyReport.class.getClassLoader()));
            }
        }
        assertTrue(out.contains(AdequacyReport.class),
                "the reports are read off what was compiled, and this found none");
        return out;
    }

    /** Whether a plurality of this type is one a report would have to put in an order. */
    private static boolean isAKind(Class<?> type) {
        return (type.isEnum() && type.getPackageName().startsWith("souther.compiler"))
                || kindsWithAnOrder().contains(type);
    }

    /** Every kind something is published in an order of, which is the sums among them. */
    private static Set<Class<?>> kindsWithAnOrder() {
        Set<Class<?>> out = new LinkedHashSet<>();
        for (Field each : PublicationOrders.class.getDeclaredFields()) {
            if (!each.getType().equals(CanonicalSelection.Order.class)) {
                continue;
            }
            each.setAccessible(true);
            try {
                Object first = ((CanonicalSelection.Order<?>) each.get(null)).slots().getFirst();
                out.add(switch (first) {
                    case Class<?> family -> family.isInterface() ? family : sealedOver(family);
                    case Enum<?> constant -> constant.getDeclaringClass();
                    default -> sealedOver(first.getClass());
                });
            } catch (IllegalAccessException opaque) {
                throw new AssertionError("an order this test cannot read: " + each.getName());
            }
        }
        assertTrue(out.size() > 1, "the kinds are read off the orders, and this found none");
        return out;
    }

    private static Class<?> sealedOver(Class<?> arm) {
        for (Class<?> each : arm.getInterfaces()) {
            if (each.isSealed()) {
                return each;
            }
        }
        return arm;
    }

    /**
     * What a value of {@code type} hands over.
     *
     * <p>What it holds and what it answers. A report reaches most of what it prints by asking —
     * {@code owed.disposition()}, {@code border.at(role)} — so a walk over fields alone reaches the
     * report's own shape and stops at the first interface, which is where everything this is about
     * begins.
     *
     * <p>Nothing an enum holds, and nothing anything answers without being asked of a value. What a
     * constant carries is its declaration's own data — a figure, a diagnostic code, the kinds a
     * criterion refuses over — and is not a plurality a compilation produced for a reader.
     */
    private static List<Member> membersOf(Class<?> type) {
        List<Member> out = new ArrayList<>();
        if (type.isEnum()) {
            return out;
        }
        if (type.isRecord()) {
            for (RecordComponent each : type.getRecordComponents()) {
                out.add(new Member(each.getName(), each.getGenericType()));
            }
        } else {
            for (Field each : type.getDeclaredFields()) {
                if (!Modifier.isStatic(each.getModifiers())) {
                    out.add(new Member(each.getName(), each.getGenericType()));
                }
            }
        }
        for (Method each : type.getMethods()) {
            if (each.getParameterCount() == 0 && !Modifier.isStatic(each.getModifiers())
                    && !each.getReturnType().equals(void.class)
                    && !each.getDeclaringClass().equals(Object.class)) {
                out.add(new Member(each.getName() + "()", each.getGenericReturnType()));
            }
        }
        return out;
    }

    /** Every class named anywhere in {@code type}, itself and what it is parameterised by. */
    private static List<Class<?>> typesIn(Type type) {
        List<Class<?>> out = new ArrayList<>();
        switch (type) {
            case Class<?> it -> out.add(it.isArray() ? it.getComponentType() : it);
            case ParameterizedType it -> {
                out.addAll(typesIn(it.getRawType()));
                for (Type each : it.getActualTypeArguments()) {
                    out.addAll(typesIn(each));
                }
            }
            case WildcardType it -> {
                for (Type each : it.getUpperBounds()) {
                    out.addAll(typesIn(each));
                }
            }
            default -> { }
        }
        return out;
    }

    /** One thing a value holds, said the same way for a record and for a class. */
    private record Member(String name, Type type) {}

    private static Class<?> rawOf(Type type) {
        return type instanceof ParameterizedType it ? rawOf(it.getRawType())
                : type instanceof Class<?> it ? it : Object.class;
    }
}
