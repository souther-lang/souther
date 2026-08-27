package souther.compiler.query;

import java.lang.reflect.Field;
import java.lang.reflect.GenericArrayType;
import java.lang.reflect.Modifier;
import java.lang.reflect.ParameterizedType;
import java.lang.reflect.Type;
import java.lang.reflect.TypeVariable;
import java.lang.reflect.WildcardType;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

/**
 * What a question declares it answers with, walked as the declarations wrote it.
 *
 * <p>The other half of the closure, and not a cheaper way of asking what a store already holds. A
 * walk of a store quantifies over what a corpus reached; this quantifies over what the compiler
 * declares, which is settled before anything is compiled. Neither contains the other: a question no
 * corpus puts is invisible to the first, and what a declaration allows is wider than what any run
 * happened to build.
 *
 * <p>What is here is what a declared type is — {@link Node} and the answers about one. The order
 * those answers are read in is {@link WhatStandsHere}'s, and the walking is {@link Traversal}'s, so
 * that a rule this keeps and the walk of a store does not is a rule neither of them can keep alone.
 *
 * <p><b>A type is what it is together with what its letters are bound to.</b> One declaration
 * reached under two sets of arguments is two shapes and holds two things, so that pair is what says
 * whether this has been here before.
 */
final class DeclaredAnswerWalk {

    /** A declared type, with whatever the way here bound its letters to. */
    record Node(Type type, Map<TypeVariable<?>, Type> bound) {}

    /** One type in one place, and why the walk stopped there. */
    record Found(TypePath.Place place, Traversal.Why why) {}

    /** What a walk of the declarations found, and how much of them it opened. */
    record Walked(List<Found> found, int opened) {}

    /** Everything the questions in {@code keys} declare that cannot be compared as a value. */
    static Walked of(List<Class<?>> keys) {
        List<Found> out = new ArrayList<>();
        int opened = 0;
        for (Class<?> key : keys) {
            Type answered = answeredBy(key);
            Traversal<Node, TypePath> walk = new Traversal<>(new OfTheDeclarations());
            walk.at(new Node(answered == null ? Key.class : answered, Map.of()), TypePath.ROOT);
            opened += walk.opened();
            for (Traversal.Stopped<TypePath> each : found(walk)) {
                out.add(new Found(each.where().of(key.getName(), each.offender()), each.why()));
            }
        }
        return new Walked(List.copyOf(out), opened);
    }

    /** What one walk of one declaration came to. A walk of types has nowhere to fall short: what it
     *  cannot settle it says at the place, and a type that reaches itself ends that path. */
    private static List<Traversal.Stopped<TypePath>> found(Traversal<Node, TypePath> walk) {
        return switch (walk.covered()) {
            case Covered.Whole<Traversal.Stopped<TypePath>>(
                    List<Traversal.Stopped<TypePath>> all) -> all;
            case Covered.Partly<Traversal.Stopped<TypePath>>(
                    List<Traversal.Stopped<TypePath>> all, List<Gap> gaps) ->
                    throw new IllegalStateException("a walk of declarations fell short: " + gaps
                            + ", having found " + all);
        };
    }

    /**
     * The type {@code key} answers with, with what a longer way round bound substituted through.
     *
     * <p>A question may reach {@link Key} through an interface of its own — what a compilation is
     * given goes through {@link Input} — and the argument it wrote is on that interface rather than
     * on this one. Read without following the binding, every such question would answer with the
     * letter its interface calls the type, which is a question this walk cannot ask anything about.
     */
    private static Type answeredBy(Class<?> key) {
        return answeredBy(key, Map.of());
    }

    private static Type answeredBy(Class<?> at, Map<TypeVariable<?>, Type> bound) {
        for (Type each : at.getGenericInterfaces()) {
            if (each instanceof ParameterizedType wrote
                    && wrote.getRawType() instanceof Class<?> raw) {
                if (raw == Key.class) {
                    return substituted(wrote.getActualTypeArguments()[0], bound);
                }
                if (Key.class.isAssignableFrom(raw)) {
                    Map<TypeVariable<?>, Type> under = new LinkedHashMap<>();
                    TypeVariable<?>[] letters = raw.getTypeParameters();
                    Type[] arguments = wrote.getActualTypeArguments();
                    for (int i = 0; i < letters.length && i < arguments.length; i++) {
                        under.put(letters[i], substituted(arguments[i], bound));
                    }
                    Type found = answeredBy(raw, under);
                    if (found != null) {
                        return found;
                    }
                }
                continue;
            }
            if (each instanceof Class<?> raw && raw != Key.class
                    && Key.class.isAssignableFrom(raw)) {
                Type found = answeredBy(raw, Map.of());
                if (found != null) {
                    return found;
                }
            }
        }
        return at.getSuperclass() == null ? null : answeredBy(at.getSuperclass(), bound);
    }

    /**
     * {@code type} with whatever {@code bound} says about the letters in it put in its place.
     *
     * <p>By the letter and not by what it is called. Two declarations may each write {@code T} and
     * they are two letters; read by name, what one of them was bound to would be read as the
     * other's.
     */
    private static Type substituted(Type type, Map<TypeVariable<?>, Type> bound) {
        return type instanceof TypeVariable<?> letter
                ? bound.getOrDefault(letter, type) : type;
    }

    /**
     * What the declarations say about one type, and nothing about the order to ask it in.
     *
     * <p>Every question here is answered of the type in front of it. Where a type is written with
     * arguments, what stands under it is read with those arguments in the letters' place, which is
     * what {@link Node} carries.
     */
    private static final class OfTheDeclarations
            implements Traversal.Walking<Node, TypePath> {

        /** What is written here once every letter and every {@code ?} has been followed. */
        private static Type settled(Node node) {
            Type type = node.type();
            if (type instanceof TypeVariable<?> letter) {
                Type found = node.bound().get(letter);
                return found == null || found == letter ? null : settled(new Node(found,
                        node.bound()));
            }
            if (type instanceof WildcardType wildcard) {
                // What stands under a bound is anything the bound admits, which is the same
                // question as a member declared as the bound.
                Type[] upper = wildcard.getUpperBounds();
                return upper.length == 1 ? settled(new Node(upper[0], node.bound())) : null;
            }
            return type;
        }

        /** The class a settled type is of, or null where it is one this cannot name. */
        private static Class<?> raw(Node node) {
            Type type = settled(node);
            return switch (type) {
                case Class<?> named -> named;
                case ParameterizedType wrote when wrote.getRawType() instanceof Class<?> named ->
                        named;
                case GenericArrayType _ -> Object[].class;
                case null, default -> null;
            };
        }

        /** What the declaration wrote in the letters' place, where it wrote any. */
        private static Type[] arguments(Node node) {
            return settled(node) instanceof ParameterizedType wrote
                    ? wrote.getActualTypeArguments() : new Type[0];
        }

        /** Everything a type this is inside binds, so that what is under it is read as written. */
        private static Map<TypeVariable<?>, Type> boundUnder(Node node, Class<?> raw) {
            Map<TypeVariable<?>, Type> under = new LinkedHashMap<>(node.bound());
            TypeVariable<?>[] letters = raw.getTypeParameters();
            Type[] arguments = arguments(node);
            for (int i = 0; i < letters.length && i < arguments.length; i++) {
                under.put(letters[i], substituted(arguments[i], node.bound()));
            }
            return under;
        }

        /**
         * What an arm binds, worked out from what the sum above it was written with.
         *
         * <p>An arm has letters of its own, and which of the sum's arguments each of them takes is
         * said by how the arm names the sum: {@code Partial<T> implements Measurement<T>} passes
         * its own letter through, and another arm may pass something else or nothing at all. Read
         * from the sum's letters instead, an arm whose letter is spelled the same would take a
         * binding meant for a different declaration.
         */
        private static Map<TypeVariable<?>, Type> boundForArm(Node node, Class<?> sum,
                                                              Class<?> arm) {
            Map<TypeVariable<?>, Type> under = new LinkedHashMap<>(node.bound());
            Map<TypeVariable<?>, Type> ofTheSum = boundUnder(node, sum);
            for (Type each : arm.isInterface() || sum.isInterface()
                    ? arm.getGenericInterfaces() : new Type[]{arm.getGenericSuperclass()}) {
                if (each instanceof ParameterizedType wrote && wrote.getRawType() == sum) {
                    Type[] passed = wrote.getActualTypeArguments();
                    TypeVariable<?>[] letters = sum.getTypeParameters();
                    for (int i = 0; i < passed.length && i < letters.length; i++) {
                        if (passed[i] instanceof TypeVariable<?> letter
                                && ofTheSum.get(letters[i]) != null) {
                            under.put(letter, ofTheSum.get(letters[i]));
                        }
                    }
                }
            }
            return under;
        }

        @Override
        public boolean bound(Node node) {
            return raw(node) != null;
        }

        @Override
        public Class<?> classOf(Node node) {
            return raw(node);
        }

        @Override
        public boolean aContainer(Node node) {
            Class<?> raw = raw(node);
            int written = arguments(node).length;
            return (Collection.class.isAssignableFrom(raw) || raw == Optional.class)
                    ? written == 1
                    : Map.class.isAssignableFrom(raw) && written == 2;
        }

        @Override
        public List<WhatStandsHere.Under<Node, TypePath>> held(Node node, TypePath where) {
            Type[] arguments = arguments(node);
            List<WhatStandsHere.Under<Node, TypePath>> out = new ArrayList<>();
            List<String> named = arguments.length == 2 ? List.of("key", "value") : List.of("held");
            for (int i = 0; i < arguments.length; i++) {
                out.add(new WhatStandsHere.Under<>(
                        where.then(new TypePath.Step.Argument(named.get(i))),
                        new Node(arguments[i], node.bound())));
            }
            return List.copyOf(out);
        }

        @Override
        public boolean closedFamily(Node node) {
            return raw(node).isSealed();
        }

        @Override
        public List<WhatStandsHere.Under<Node, TypePath>> arms(Node node, TypePath where) {
            Class<?> sum = raw(node);
            List<WhatStandsHere.Under<Node, TypePath>> out = new ArrayList<>();
            for (Class<?> arm : sum.getPermittedSubclasses()) {
                out.add(new WhatStandsHere.Under<>(
                        where.then(new TypePath.Step.Arm(arm.getTypeName())),
                        new Node(arm, boundForArm(node, sum, arm))));
            }
            return List.copyOf(out);
        }

        /**
         * Whether a thing of this may itself be built.
         *
         * <p>Nothing is ever of an interface or of something abstract: what stands there is of
         * something under it, which is a different question from what this declares.
         */
        @Override
        public boolean itselfStands(Node node) {
            Class<?> raw = raw(node);
            return !raw.isInterface() && !Modifier.isAbstract(raw.getModifiers());
        }

        @Override
        public boolean closesWhatStandsHere(Node node) {
            return Modifier.isFinal(raw(node).getModifiers());
        }

        @Override
        public List<WhatStandsHere.Under<Node, TypePath>> members(Node node, TypePath where) {
            Class<?> raw = raw(node);
            Map<TypeVariable<?>, Type> under = boundUnder(node, raw);
            List<WhatStandsHere.Under<Node, TypePath>> out = new ArrayList<>();
            for (Field field : AnswerShape.fieldsOf(raw)) {
                out.add(new WhatStandsHere.Under<>(
                        where.thenMember(field.getDeclaringClass(), field.getName()),
                        new Node(field.getGenericType(), under)));
            }
            return List.copyOf(out);
        }

        /** A type and what its letters are bound to, which is what makes two of these one shape. */
        @Override
        public Object keyOf(Node node) {
            return new Node(settled(node), node.bound());
        }

        @Override
        public String named(Node node) {
            Type type = settled(node);
            return type == null ? node.type().getTypeName()
                    : type instanceof ParameterizedType wrote
                            ? wrote.getRawType().getTypeName() : type.getTypeName();
        }

        /** A declaration that reaches itself is a shape and not a defect: what is under it is being
         *  asked about where it was first met, so this path ends here. */
        @Override
        public Gap aLoop(Node node, TypePath where) {
            return null;
        }
    }

    private DeclaredAnswerWalk() {
    }
}
