package souther.compiler.query;

import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.Collection;
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
 * <p>What is here is what an object is — {@link WhatStandsHere.Facts} answered of one. The order
 * those answers are read in is {@link WhatStandsHere}'s and the walking is {@link Traversal}'s, so
 * that this and the walk of the declarations cannot come apart over a rule either of them keeps.
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
     * What the walk found and how much of the store it went into, beside what it met on the way —
     * which is what says a walk reached the answers a caller is asking about at all.
     *
     * @param opened how many things it went into what they hold, which counts neither a leaf nor
     *               something it stopped at
     */
    record Walked(int opened, Set<String> classes, Covered<Found> covered) {}

    private AnswerWalk() {
    }

    /** Everything {@code db} holds, walked. */
    static Walked of(Db db) {
        List<Found> out = new ArrayList<>();
        List<Gap> gaps = new ArrayList<>();
        Set<String> classes = new LinkedHashSet<>();
        int visited = 0;
        for (Map.Entry<Key<?>, Answer<?>> each : db.everyAnswer().entrySet()) {
            visited += into(each.getKey().getClass().getName(), each.getValue(), out, gaps,
                    classes);
        }
        return new Walked(visited, classes, Covered.of(List.copyOf(out), List.copyOf(gaps)));
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
        List<Found> out = new ArrayList<>();
        List<Gap> gaps = new ArrayList<>();
        Set<String> classes = new LinkedHashSet<>();
        int visited = into(question, root, out, gaps, classes);
        return new Walked(visited, classes, Covered.of(List.copyOf(out), List.copyOf(gaps)));
    }

    private static int into(String question, Object root, List<Found> out, List<Gap> gaps,
                            Set<String> classes) {
        OfOneStore facts = new OfOneStore(question, classes);
        Traversal<Object, Locus> walk = new Traversal<>(facts);
        facts.walk = walk;
        walk.at(root, Locus.ROOT);
        switch (walk.covered()) {
            case Covered.Whole<Traversal.Stopped<Locus>>(List<Traversal.Stopped<Locus>> all) ->
                    all.forEach(each -> out.add(
                            new Found(question, each.offender(), each.where())));
            case Covered.Partly<Traversal.Stopped<Locus>>(
                    List<Traversal.Stopped<Locus>> all, List<Gap> fellShort) -> {
                all.forEach(each -> out.add(
                        new Found(question, each.offender(), each.where())));
                gaps.addAll(fellShort);
            }
        }
        return walk.opened();
    }

    /**
     * What one object is, and nothing about the order to ask it in.
     *
     * <p>Everything here is asked of the object in front of the walk. What may stand somewhere is
     * not a question a store can be asked — the object standing there is the answer — so what is
     * closed and what is a sum are the declarations' business and are said to be settled here.
     */
    private static final class OfOneStore implements Traversal.Walking<Object, Locus> {

        private final String question;
        private final Set<String> classes;
        private Traversal<Object, Locus> walk;

        OfOneStore(String question, Set<String> classes) {
            this.question = question;
            this.classes = classes;
        }

        @Override
        public boolean bound(Object node) {
            return true;
        }

        @Override
        public Class<?> classOf(Object node) {
            classes.add(node.getClass().getName());
            return node.getClass();
        }

        /**
         * Whether what is here stands for what it holds.
         *
         * <p>Asked of what it turned out to be and not of what anything was written as: a store
         * hands over the object, and its class is what the walk has.
         */
        @Override
        public boolean aContainer(Object node) {
            return AnswerShape.standsForWhatItHolds(node.getClass());
        }

        @Override
        public Covered<WhatStandsHere.Under<Object, Locus>> held(Object node, Locus where) {
            List<WhatStandsHere.Under<Object, Locus>> out = new ArrayList<>();
            switch (node) {
                case Collection<?> items -> items.forEach(each ->
                        under(out, where.then(new Locus.Step.Element()), each));
                // What an absence may be hiding. Read through rather than walked into: the field
                // under it belongs to `java.base`, which opens nothing to this.
                case Optional<?> maybe -> maybe.ifPresent(each ->
                        under(out, where.then(new Locus.Step.Present()), each));
                case Map<?, ?> entries -> entries.forEach((key, value) -> {
                    under(out, where.then(new Locus.Step.MapKey()), key);
                    under(out, where.then(new Locus.Step.MapValue()), value);
                });
                default -> throw new IllegalStateException("not a container: " + node.getClass());
            }
            return Covered.of(List.copyOf(out), List.of());
        }

        /** Nothing is at a place that holds nothing, and nothing is what it says about itself. */
        private static void under(List<WhatStandsHere.Under<Object, Locus>> out, Locus where,
                                  Object held) {
            if (held != null) {
                out.add(new WhatStandsHere.Under<>(where, held));
            }
        }

        /** An object is of the class it is of, and what else that class permits is a question
         *  about the declarations rather than about this. */
        @Override
        public boolean closedFamily(Object node) {
            return false;
        }

        @Override
        public Covered<WhatStandsHere.Under<Object, Locus>> arms(Object node, Locus where) {
            return Covered.of(List.of(), List.of());
        }

        @Override
        public boolean itselfStands(Object node) {
            return true;
        }

        @Override
        public boolean closesWhatStandsHere(Object node) {
            return true;
        }

        @Override
        public Covered<WhatStandsHere.Under<Object, Locus>> members(Object node, Locus where) {
            List<WhatStandsHere.Under<Object, Locus>> out = new ArrayList<>();
            List<Gap> fellShort = new ArrayList<>();
            for (Field field : AnswerShape.fieldsOf(node.getClass())) {
                Locus at = where.thenMember(field.getDeclaringClass(), field.getName());
                Object held;
                try {
                    field.setAccessible(true);
                    held = field.get(node);
                } catch (RuntimeException | ReflectiveOperationException opaque) {
                    // A field this cannot open is a subtree it did not ask about, and what comes
                    // back says so: read as everything this holds, it would be a thing half looked
                    // at that nothing could tell from one looked at whole.
                    fellShort.add(new Gap(Gap.Why.A_FIELD_THAT_WOULD_NOT_OPEN,
                            question + at.asText()));
                    continue;
                }
                under(out, at, held);
            }
            return Covered.of(List.copyOf(out), List.copyOf(fellShort));
        }

        /** Two objects are the same thing when they are the same object. */
        @Override
        public Object keyOf(Object node) {
            return new Itself(node);
        }

        @Override
        public String named(Object node) {
            // A lambda's class name carries the JVM's own counter, which differs per run. What is
            // left is what the type is called, which is what the other walk calls it too, so a
            // register keyed by what was found holds one line for a thing whichever met it.
            return node.getClass().getTypeName().replaceFirst("/0x[0-9a-f]+$", "");
        }

        /** An object graph that holds itself is one nobody meant to walk, and what is under it went
         *  unasked. */
        @Override
        public Gap aLoop(Object node, Locus where) {
            return new Gap(Gap.Why.A_GRAPH_THAT_LOOPS,
                    question + where.asText() + " " + node.getClass().getName());
        }
    }

    /** One object, by which object it is. */
    private record Itself(Object held) {

        @Override
        public boolean equals(Object other) {
            return other instanceof Itself that && that.held == held;
        }

        @Override
        public int hashCode() {
            return System.identityHashCode(held);
        }
    }
}
