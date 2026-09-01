package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.check.ElementBindings;
import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.Type;

import java.lang.reflect.Constructor;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.lang.reflect.RecordComponent;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * An answer this reading gives carries what makes it that answer, and refuses to be made without it.
 *
 * <p>Every one of them is a distinction: a position reached against one that names none, an edge to
 * go on through against one this question refuses, a name that is a parameter against one nothing
 * was said of. An answer made without what it carries is the same distinction lost — a position that
 * is no position reads, to anything that goes on to use it, as the answer beside it. Left to the one
 * place that builds each, the guarantee holds for as long as nobody adds a second place.
 *
 * <p><b>Over what this reading publishes, and not over a list.</b> The population is walked from the
 * answers {@link InputReads} hands out and the shapes inside them, stopping where a type belongs to
 * somebody else: what the language's own trees carry is that language's rule, and an answer of this
 * reading that quotes one is not thereby answering for it. So an answer added here is in scope
 * without anyone adding it, which is the whole of why this is a walk rather than a list.
 *
 * <p>Written after three of these were found one at a time. What each of them had in common was not
 * the shape of the value but that the rule lived in prose, so the next one was found by a reader
 * rather than by the build.
 */
class EveryAnswerThisReadingPublishesCarriesWhatMakesItOneTest {

    /** What makes an answer that answer, over every answer this reading publishes. */
    @Test
    void everyAnswerRefusesToBeMadeWithoutWhatItCarries() {
        List<String> lost = new ArrayList<>();
        List<String> held = new ArrayList<>();
        for (Class<?> each : published()) {
            RecordComponent[] parts = each.isRecord() ? each.getRecordComponents() : null;
            if (parts == null || Arrays.stream(parts).allMatch(p -> p.getType().isPrimitive())) {
                continue;
            }
            List<String> without = lostPayloadsOf(each, parts);
            lost.addAll(without);
            if (without.isEmpty()) {
                held.add(each.getSimpleName());
            }
        }
        assertFalse(held.isEmpty(),
                "the walk reaches the answers, so an empty run is a broken walk and not a clean one");
        assertEquals(List.of(), lost,
                () -> "each of these is something an answer says it carries and can be made"
                        + " without, so a reader is told of it and finds nothing; held: " + held);
    }

    /**
     * The answers this reading gives, and the shapes inside them.
     *
     * <p>From both of the things that answer: what a reader outside is given
     * ({@link InputReads}) and what the walks inside are given ({@link BindingEnvironment}). The
     * second is where the answers this reading was getting wrong live — which is a reason to walk
     * from it and not a reason to leave it out, since a distinction lost inside is lost for
     * everything built on it.
     *
     * <p>Stopping at the package boundary: a {@code Core} an answer quotes is the language's tree
     * and what it must carry is the language's rule, not this one's.
     */
    private static Set<Class<?>> published() {
        Set<Class<?>> found = new LinkedHashSet<>();
        for (Class<?> answering : List.of(InputReads.class, BindingEnvironment.class)) {
            for (Method each : answering.getDeclaredMethods()) {
                if (!Modifier.isPrivate(each.getModifiers())) {
                    collect(each.getReturnType(), found);
                }
            }
        }
        return found;
    }

    private static void collect(Class<?> type, Set<Class<?>> into) {
        if (type == null || !type.getName().startsWith("souther.compiler.inputs.")
                || !into.add(type)) {
            return;
        }
        Class<?>[] permitted = type.getPermittedSubclasses();
        if (permitted != null) {
            for (Class<?> each : permitted) {
                collect(each, into);
            }
        }
        if (type.isRecord()) {
            for (RecordComponent part : type.getRecordComponents()) {
                collect(part.getType(), into);
            }
        }
    }

    /**
     * Which of {@code each}'s payloads it can be built without, of the ones it carries.
     *
     * <p>One at a time, with the rest given something. Emptied all at once, an answer carrying two
     * is held to nothing more than that it cannot lose both — the first check to survive answers for
     * the others, and a payload whose own check went missing is covered by whichever one is left.
     * What is claimed here is of each of them, so each of them is what is asked.
     */
    private static List<String> lostPayloadsOf(Class<?> each, RecordComponent[] parts) {
        List<String> lost = new ArrayList<>();
        for (int missing = 0; missing < parts.length; missing++) {
            if (parts[missing].getType().isPrimitive()) {
                continue;
            }
            Object[] args = new Object[parts.length];
            for (int i = 0; i < parts.length; i++) {
                args[i] = i == missing ? null : something(parts[i].getType());
            }
            if (built(each, parts, args)) {
                lost.add(each.getSimpleName() + "." + parts[missing].getName());
            }
        }
        return lost;
    }

    /** Whether {@code each} can be built from {@code args}. */
    private static boolean built(Class<?> each, RecordComponent[] parts, Object[] args) {
        try {
            Constructor<?> ctor = each.getDeclaredConstructor(Arrays.stream(parts)
                    .map(RecordComponent::getType).toArray(Class<?>[]::new));
            ctor.setAccessible(true);
            ctor.newInstance(args);
            return true;
        } catch (ReflectiveOperationException e) {
            return false;
        }
    }

    /**
     * Something of {@code type} for a payload that is not the one being taken away.
     *
     * <p>A type nothing here can make is refused rather than skipped. Skipped, an answer carrying a
     * shape this does not know would be held to nothing at all, and the walk would go on reporting
     * that every answer it reached was held — which is the reading of an empty answer this test
     * exists to refuse.
     */
    private static Object something(Class<?> type) {
        if (type.isPrimitive()) {
            return type == boolean.class ? Boolean.FALSE : 0;
        }
        if (type == String.class) {
            return "x";
        }
        if (type == List.class) {
            return List.of();
        }
        if (type == TermPath.class) {
            return TermPath.of("x");
        }
        if (type == Core.class) {
            return SOMETHING;
        }
        if (type == InputReads.class) {
            return NOWHERE;
        }
        if (type == Denotation.class) {
            return new Denotation(SOMETHING, NOWHERE);
        }
        if (type == BindingId.class) {
            return new BindingId(new BindingOwner.OfValue("example", "f"), 0);
        }
        throw new IllegalStateException("nothing here makes a " + type.getName()
                + ", so an answer carrying one would be held to nothing");
    }

    private static final Core SOMETHING =
            new Core.Int(0, Type.INT, new SourcePos(0, 0));

    private static final InputReads NOWHERE =
            InputReads.ofParameters(Map.of(), ElementBindings.NONE);
}
