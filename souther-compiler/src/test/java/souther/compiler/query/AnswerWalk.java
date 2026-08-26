package souther.compiler.query;

import java.lang.reflect.Array;
import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * One store's answers walked, with each object asked whether it means anything by {@code equals}.
 *
 * <p>The other of the two detectors, beside {@link Divergence}. This one holds one answer and asks
 * each object under it what it is; that one holds two and asks where they come apart. Neither sees
 * what the other does — a class with no {@code equals} is found here whether or not two compiles
 * ever disagree over it, and a class whose {@code equals} rests on an address has one and is found
 * only by comparing.
 *
 * <p><b>The object before what it holds.</b> Whether a thing means anything by {@code equals} is
 * asked of it first, and only then is it walked into. Asked the other way round — walk a container,
 * ask a plain object — an array is stepped through and never questioned, and an array's equality is
 * its address whatever it holds.
 *
 * <p><b>From the answer and not from its value.</b> An answer is what it holds and what the compile
 * said getting there, and {@code Db} compares both to stop work. Started at the value, this would
 * promise less than the store relies on.
 */
final class AnswerWalk {

    /** One thing that compares by address, and the place in an answer that holds it. */
    record Found(String question, String offender, Locus at) {

        /** Which answer, where in it, and what — which is what a register of places is keyed by. */
        Locus.Place place() {
            return at.of(question, offender);
        }
    }

    /**
     * What the walk found, and how much of the store it covered.
     *
     * <p>The coverage beside the findings rather than swallowed. A field the runtime will not hand
     * over is a subtree nothing asked about, and a graph that holds itself is walked from one place
     * only — both leave a walk covering less than it looks like it covered, and a register agreeing
     * with one of those agrees about less than it names.
     */
    record Walked(int visited, Set<String> classes, List<Found> found,
                  Set<String> notOpened, Set<String> loops) {

        /** Whether the walk got to the end of what there was to walk. */
        boolean complete() {
            return notOpened.isEmpty() && loops.isEmpty();
        }

        /** Every place one of them sits. */
        Set<Locus.Place> places() {
            Set<Locus.Place> out = new java.util.TreeSet<>();
            found.forEach(each -> out.add(each.place()));
            return out;
        }
    }

    private AnswerWalk() {
    }

    /** Everything {@code db} holds, walked. */
    static Walked of(Db db) {
        Scan scan = new Scan();
        db.everyAnswer().forEach((key, answer) -> {
            scan.question = key.getClass().getName();
            scan.at(answer, Locus.ROOT);
        });
        return scan.walked();
    }

    /**
     * One thing walked as though it were the answer to {@code question}.
     *
     * <p>For a test that builds the shape it is about rather than compiling for one. What this walk
     * answers cannot be seen from a store: a store holds whatever the compiler happens to hold, and
     * a walk that names a holder instead of what it holds, or steps over a container without asking
     * it anything, comes back from one looking exactly like a walk that did neither.
     */
    static Walked of(String question, Object root) {
        Scan scan = new Scan();
        scan.question = question;
        scan.at(root, Locus.ROOT);
        return scan.walked();
    }

    /** Whether {@code type} says what it is, rather than which object it is. */
    private static boolean declaresEquals(Class<?> type) {
        try {
            return type.getMethod("equals", Object.class).getDeclaringClass() != Object.class;
        } catch (NoSuchMethodException none) {
            return false;
        }
    }

    /**
     * One walk of everything a store holds.
     *
     * <p>Every place and not every object. One object under an answer is held by however many paths
     * hold it, and each of those is a place the answer exposes it — so what is remembered per object
     * is what was found under it, written out again at each path that reaches it. Remembered as
     * "already seen", the second path would come back with nothing and a register of places would
     * hold whichever path the walk happened to take first.
     */
    private static final class Scan {

        private final Map<Object, List<Found>> settled = new IdentityHashMap<>();
        private final Set<Object> walking = Collections.newSetFromMap(new IdentityHashMap<>());
        private final Set<Object> visited = Collections.newSetFromMap(new IdentityHashMap<>());
        private final Set<String> classes = new LinkedHashSet<>();
        private final List<Found> out = new ArrayList<>();
        private final Set<String> notOpened = new LinkedHashSet<>();
        private final Set<String> loops = new LinkedHashSet<>();
        /** Which answer the walk is inside, so a place says which question holds it. */
        private String question = "";

        Walked walked() {
            return new Walked(visited.size(), classes, List.copyOf(out), notOpened, loops);
        }

        /** @return whether what is under {@code each} was covered, so a caller may remember it */
        boolean at(Object each, Locus where) {
            if (each == null) {
                return true;
            }
            // The leaves. A boxed number, a string, a case of an enumeration and a class are values
            // by the language, and asking them again would be asking about the JDK.
            if (each instanceof String || each instanceof Number || each instanceof Boolean
                    || each instanceof Character || each instanceof Enum<?>
                    || each instanceof Class<?>) {
                return true;
            }
            List<Found> already = settled.get(each);
            if (already != null) {
                already.forEach(found -> out.add(new Found(
                        question, found.offender(), where.followedBy(found.at()))));
                return true;
            }
            if (!walking.add(each)) {
                loops.add(each.getClass().getName() + " at " + where);
                return false;
            }
            visited.add(each);
            int before = out.size();
            boolean whole;
            try {
                whole = under(each, where);
            } finally {
                walking.remove(each);
            }
            if (whole) {
                List<Found> mine = new ArrayList<>();
                for (Found found : out.subList(before, out.size())) {
                    mine.add(new Found(found.question(), found.offender(),
                            new Locus(found.at().steps()
                                    .subList(where.steps().size(), found.at().steps().size()))));
                }
                settled.put(each, List.copyOf(mine));
            }
            return whole;
        }

        private boolean under(Object each, Locus where) {
            classes.add(each.getClass().getName());
            if (!declaresEquals(each.getClass())) {
                // A lambda's class name carries the JVM's own counter, which differs per run, and an
                // array is named the way the other detector names one, so a register keyed by what
                // was found holds one line for a thing whichever walk met it.
                out.add(new Found(question, each.getClass().isArray()
                        ? each.getClass().getSimpleName()
                        : each.getClass().getName().replaceFirst("/0x[0-9a-f]+$", ""), where));
                return true;    // what it holds is unreachable through an equality that never holds
            }
            if (each instanceof Collection<?> items) {
                boolean whole = true;
                for (Object item : items) {
                    whole &= at(item, where.then(new Locus.Step.Element()));
                }
                return whole;
            }
            // What an absence may be hiding. Read through rather than walked into: the field under
            // it belongs to `java.base`, which opens nothing to this, so an answer holding one of
            // these would have every object beneath it go unasked.
            if (each instanceof Optional<?> maybe) {
                return maybe.isEmpty() || at(maybe.get(), where.then(new Locus.Step.Present()));
            }
            if (each instanceof Map<?, ?> entries) {
                boolean whole = true;
                for (Map.Entry<?, ?> entry : entries.entrySet()) {
                    whole &= at(entry.getKey(), where.then(new Locus.Step.MapKey()));
                    whole &= at(entry.getValue(), where.then(new Locus.Step.MapValue()));
                }
                return whole;
            }
            if (each.getClass().isArray()) {
                boolean whole = true;
                for (int i = 0; i < Array.getLength(each); i++) {
                    whole &= at(Array.get(each, i), where.then(new Locus.Step.Element()));
                }
                return whole;
            }
            return fieldsOf(each, where);
        }

        private boolean fieldsOf(Object each, Locus where) {
            boolean whole = true;
            for (Class<?> at = each.getClass(); at != null && at != Object.class;
                    at = at.getSuperclass()) {
                for (Field field : at.getDeclaredFields()) {
                    if (Modifier.isStatic(field.getModifiers()) || field.getType().isPrimitive()) {
                        continue;
                    }
                    Object held;
                    try {
                        field.setAccessible(true);
                        held = field.get(each);
                    } catch (RuntimeException | ReflectiveOperationException opaque) {
                        // A field this cannot open is a subtree it did not ask about. Said out loud,
                        // because what is under it would otherwise be counted as looked at and clean.
                        notOpened.add(at.getName() + "." + field.getName());
                        whole = false;
                        continue;
                    }
                    whole &= at(held, where.thenMember(at, field.getName()));
                }
            }
            return whole;
        }
    }
}
