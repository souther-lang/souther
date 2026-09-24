package souther.compiler.meta;

import souther.compiler.ast.Hir;

import java.lang.reflect.Method;
import java.lang.reflect.Type;
import java.util.ArrayList;
import java.util.List;

/**
 * Which parts of a declaration a crossing depends on, said once for the walk and for a sweep.
 *
 * <p>The walk reads values off a declaration and a sweep reads the types those parts are declared
 * to hold. Written twice, the two come apart the first time a part joins one of them: the walk
 * compares something no sweep has said anything about, or a sweep asks for an account of a part no
 * crossing reads. Both are the shape this comparison keeps running into — an account taken from
 * somewhere other than the decision — so what is taken is written here and read from both sides.
 *
 * <p>What is taken and not what is done with it. Whether the comparison passes a part over, walks
 * inside it or hands it to its own equality is the other question and is answered where that
 * reading is written. This says only which parts of a declaration a crossing is about at all.
 *
 * <p>The declarations themselves are not listed here. Which kinds of declaration there are is a
 * switch in {@link DeclarationAgreement}, so that a kind added later is a compile error rather than
 * a form silently compared by nothing; what each of them takes is here.
 */
final class CrossingProjection {

    private CrossingProjection() {}

    /**
     * How a part of a declaration turns into what is compared.
     *
     * <p>Three, because the list a part holds is not always compared as a list of what it holds. A
     * behavior's parameters cross as the types it takes, one element each; a data's fields cross as
     * what each is called together with what it holds, which is a pair per field. Both are written
     * out rather than worked out from how many sub-parts are named, so that naming a second sub-part
     * of a parameter does not quietly change the shape every comparison of a signature reads.
     */
    private enum Shape {
        /** The part itself, whatever it holds. */
        WHOLE,
        /** Of each element, the one sub-part named, in the element's place. */
        EACH_FLATTENED,
        /** Of each element, the sub-parts named, as a list in the element's place. */
        EACH_AS_A_LIST
    }

    /**
     * One part a crossing depends on: what it is called, how to read it, and what of its elements
     * is taken.
     *
     * @param name  what the declaration calls it, which is what the reader here is looked up by
     * @param read  the no-argument method that answers it
     * @param shape whether the part crosses whole or element by element
     * @param ofEach what is taken of each element, empty unless the shape says elements
     */
    record Taken(String name, Method read, Shape shape, List<Taken> ofEach) {

        /** The type this part is declared to hold, which is what a sweep is held to. */
        Type held() {
            return read.getGenericReturnType();
        }
    }

    /**
     * Everything a product declaration is: which declaration it is, whether it is a newtype (which
     * is what it is represented as), what it includes and holds, and what it admits.
     *
     * <p>How a value of it crosses is read off exactly those, so comparing the derived
     * representation as well would be comparing the same fact twice — and these are declarations as
     * resolution left them, where nothing has derived one.
     *
     * <p>A field's name is not a name of something else — it is what a decoder reads a value under,
     * so it is part of what the declaration says. Every other name in a declaration reaches something
     * and is compared as what it reaches; this one is compared as the word it is.
     */
    static final List<Taken> OF_A_PRODUCT = List.of(
            whole(Hir.Data.class, "declares"),
            whole(Hir.Data.class, "newtype"),
            whole(Hir.Data.class, "includes"),
            eachAsAList(Hir.Data.class, "fields", Hir.Field.class, "name", "type"),
            whole(Hir.Data.class, "invariants"));

    /**
     * Which cases a sum has.
     *
     * <p>How one is told from another is derived from that and from what each case is
     * ({@code check.Boundary}), and both are reached: a case is followed to its own declaration,
     * where a unit and a product are compared as the different forms they are. Held here as well, it
     * would be the same fact compared twice.
     */
    static final List<Taken> OF_A_SUM = List.of(
            whole(Hir.SumData.class, "declares"),
            whole(Hir.SumData.class, "cases"));

    /** A unit is the declaration it is, which is what it was looked up by. */
    static final List<Taken> OF_A_UNIT = List.of(
            whole(Hir.UnitData.class, "declares"));

    /**
     * What a behavior takes and what it answers with.
     *
     * <p>What a parameter is called is not part of what crosses: arguments are handed over by
     * position, and a signature whose parameters are renamed takes what it took.
     */
    static final List<Taken> OF_A_DECLARED_BEHAVIOR = List.of(
            eachFlattened(Hir.SpecBehavior.class, "params", Hir.Param.class, "type"),
            whole(Hir.SpecBehavior.class, "ret"),
            whole(Hir.SpecBehavior.class, "constructs"),
            whole(Hir.SpecBehavior.class, "dependsOn"),
            whole(Hir.SpecBehavior.class, "ensures"));

    /**
     * What a composition another project compiled takes and what it answers with.
     *
     * <p>That is all a module publishes of one ({@link Hir.Composition.Elsewhere}): its stages stay
     * behind, so which stages it has is nothing two builds can be held to.
     */
    static final List<Taken> OF_A_PUBLISHED_COMPOSITION = List.of(
            whole(Hir.Composition.Elsewhere.class, "takes"),
            whole(Hir.Composition.Elsewhere.class, "answers"));

    /**
     * A published helper, whole.
     *
     * <p>These are carried because a declaration cannot be read without them — an invariant calls
     * them, a published value is a definition the reader's analyses read — so a helper that computes something
     * else makes the declaration carrying it admit something else. There is no part of one that a
     * crossing does not depend on.
     */
    static final List<Taken> OF_A_HELPER = List.of(
            whole(Hir.FnDef.class, "params"),
            whole(Hir.FnDef.class, "declaredReturn"),
            whole(Hir.FnDef.class, "body"),
            whole(Hir.FnDef.class, "modifiers"));

    /** What {@code declaration} says, as the parts a crossing depends on. */
    static List<Object> read(List<Taken> taken, Object declaration) {
        List<Object> parts = new ArrayList<>();
        for (Taken one : taken) {
            Object held = answer(one, declaration);
            switch (one.shape()) {
                case WHOLE -> parts.add(held);
                // One part and not one per element. What a declaration takes is the same part
                // however many elements it has, so two declarations differing in how many they
                // have differ in that part rather than in how many parts there are.
                case EACH_FLATTENED -> {
                    List<Object> ofEach = new ArrayList<>();
                    for (Object element : (List<?>) held) {
                        ofEach.add(answer(one.ofEach().getFirst(), element));
                    }
                    parts.add(ofEach);
                }
                case EACH_AS_A_LIST -> {
                    List<Object> ofEach = new ArrayList<>();
                    for (Object element : (List<?>) held) {
                        List<Object> ofOne = new ArrayList<>();
                        for (Taken sub : one.ofEach()) {
                            ofOne.add(answer(sub, element));
                        }
                        ofEach.add(ofOne);
                    }
                    parts.add(ofEach);
                }
            }
        }
        return parts;
    }

    /**
     * The types these parts are declared to hold, which is where a sweep over what a crossing
     * reaches begins.
     *
     * <p>The element of a part taken element by element is not among them. What crosses there is
     * what is taken of each element and never the element itself, so a sweep starting at the element
     * would reach every part of it — which is the sweep asking for an account of what no crossing
     * reads.
     */
    static List<Type> rootsOf(List<Taken> taken) {
        List<Type> roots = new ArrayList<>();
        for (Taken one : taken) {
            if (one.shape() == Shape.WHOLE) {
                roots.add(one.held());
            } else {
                for (Taken sub : one.ofEach()) {
                    roots.add(sub.held());
                }
            }
        }
        return roots;
    }

    private static Taken whole(Class<?> owner, String name) {
        return new Taken(name, answering(owner, name), Shape.WHOLE, List.of());
    }

    private static Taken eachFlattened(Class<?> owner, String name, Class<?> element, String sub) {
        return new Taken(name, answering(owner, name), Shape.EACH_FLATTENED,
                List.of(whole(element, sub)));
    }

    private static Taken eachAsAList(Class<?> owner, String name, Class<?> element,
            String... subs) {
        List<Taken> ofEach = new ArrayList<>();
        for (String sub : subs) {
            ofEach.add(whole(element, sub));
        }
        return new Taken(name, answering(owner, name), Shape.EACH_AS_A_LIST, List.copyOf(ofEach));
    }

    private static Method answering(Class<?> owner, String name) {
        try {
            return owner.getMethod(name);
        } catch (NoSuchMethodException e) {
            throw new IllegalStateException(owner.getName() + " is written here as taking `" + name
                    + "` and answers nothing by that name, so what a crossing depends on names a"
                    + " part of a declaration that is not there.", e);
        }
    }

    private static Object answer(Taken taken, Object of) {
        try {
            return taken.read().invoke(of);
        } catch (ReflectiveOperationException e) {
            throw new IllegalStateException("a part that cannot be read: " + taken.name(), e);
        }
    }

}
