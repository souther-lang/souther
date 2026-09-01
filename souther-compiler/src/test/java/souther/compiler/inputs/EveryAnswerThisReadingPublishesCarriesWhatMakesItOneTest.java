package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import java.lang.reflect.Constructor;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.lang.reflect.RecordComponent;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashSet;
import java.util.List;
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
        List<String> admits = new ArrayList<>();
        List<String> held = new ArrayList<>();
        for (Class<?> each : published()) {
            RecordComponent[] parts = each.isRecord() ? each.getRecordComponents() : null;
            if (parts == null || Arrays.stream(parts).allMatch(p -> p.getType().isPrimitive())) {
                continue;
            }
            (refusesNulls(each, parts) ? held : admits).add(each.getSimpleName());
        }
        assertFalse(held.isEmpty(),
                "the walk reaches the answers, so an empty run is a broken walk and not a clean one");
        assertEquals(List.of(), admits,
                () -> "each of these can be made without what makes it the answer it is, and read"
                        + " as the answer beside it; held: " + held);
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

    /** Whether {@code each} refuses to be built with nothing where it carries something. */
    private static boolean refusesNulls(Class<?> each, RecordComponent[] parts) {
        try {
            Constructor<?> ctor = each.getDeclaredConstructor(Arrays.stream(parts)
                    .map(RecordComponent::getType).toArray(Class<?>[]::new));
            ctor.setAccessible(true);
            Object[] args = new Object[parts.length];
            for (int i = 0; i < parts.length; i++) {
                args[i] = parts[i].getType().isPrimitive() ? Boolean.FALSE : null;
            }
            ctor.newInstance(args);
            return false;
        } catch (ReflectiveOperationException e) {
            return true;
        }
    }
}
