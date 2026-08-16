package souther.compiler.diag;

import org.junit.jupiter.api.Test;

import souther.compiler.source.SourceId;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.lang.reflect.Constructor;
import java.lang.reflect.Executable;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.lang.reflect.Parameter;
import java.lang.reflect.GenericArrayType;
import java.lang.reflect.ParameterizedType;
import java.lang.reflect.RecordComponent;
import java.lang.reflect.Type;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * No value holds a source identity beside something that already answers for one.
 *
 * <p>This is the shape #760 turned out to be, and it was found four times by eye before it was
 * written down. Each time the answer was the same: a value held a source next to a region or a
 * coordinate that carries one, the two could disagree, and nothing kept them the same. A renderer
 * takes them apart again — the file to quote from, the numbers to quote at — so a pair that
 * disagrees is a marker put in one file with its line read from another.
 *
 * <p>The rule is written on {@link Placement}: <em>a source location has exactly one authority for
 * its provenance</em>. A rule a reviewer has to notice is a rule that gets noticed four times and
 * missed the fifth, so it is checked here as well.
 *
 * <h2>Why this can be checked at all</h2>
 *
 * <p>It could not be, once. A source was a {@code String} and so is a message, the build keeps no
 * parameter names, and nothing in a signature told them apart — so what this asked was two narrower
 * questions of a list of classes somebody kept up to date. A list is the proposition written a
 * second time: a value added tomorrow and left off it is a value nothing here says anything about,
 * and the list stays green.
 *
 * <p>{@link SourceId} is what made the question askable. Now every class the compiler and its
 * syntax produce is read, with nothing named on either side: what a source identity is, is a type,
 * and so is what answers for one.
 *
 * <p>Through the wrapping, and not only at the top. The field this change removed was
 * {@code Optional<SourceRef>}, so a check that compared erased types would have watched that shape
 * go and said nothing when it came back — green for the very value it was written about. And by
 * what a type is rather than which type it is: a value holding the record under a sealed arm
 * answers for a source exactly as one holding the arm does.
 *
 * <h2>What it does not reach</h2>
 *
 * <p>The classes on this test's path, which is this module's and the syntax module's. An editor and
 * a command line hold sources of their own under names of their own, and neither is here.
 */
class NoValueHoldsASourceBesideOneThatAnswersForItTest {

    /**
     * The types that answer for a source of their own, so holding one beside them is holding two
     * answers to one question.
     *
     * <p>Roots, and read by assignability. `Citation` is sealed over two arms and each arm over one
     * record, so a set that named the classes there are today would go quiet the moment a value held
     * `WrittenCitation` rather than `Citation` — a list of the enumeration this test exists to stop
     * being written, one level down from the one it replaced.
     */
    private static final Set<Class<?>> ANSWERS_FOR_A_SOURCE = Set.of(
            Region.class, SourcePos.class, DiagnosticPlace.InSource.class, Citation.class,
            Diagnostic.class);

    /**
     * Nothing. The one value that used to hold both was {@link Spot}, which paired a told source
     * with a region because a primary region was not held to naming one — and what the told source
     * meant depended on which of them it was beside: the source the region was in, or the file the
     * report was being read from.
     *
     * <p>Both are values now and neither is told. A place a reader is sent to carries its source
     * ({@link Spot.InSource}); a place in a text this compilation cannot name carries the text the
     * surface says it is reading, which is not a second answer to a question its region answers,
     * because that region answers nothing ({@link UnnamedRegion}). Which file a report is listed
     * under is the third thing and is not a place at all — it is what a caller holding the files
     * answers, and it is on the context rather than beside the report.
     *
     * <p>Kept as an empty set rather than deleted. An exception admitted here is a rule this test
     * stops making, and one added later should look like what it is.
     */
    private static final Set<Class<?>> OPEN = Set.of();

    private static final List<Class<?>> COMPILED = compiled();

    @Test
    void noValueHoldsASourceIdentityBesideAPlaceThatAnswersForOne() {
        List<String> holding = new ArrayList<>();
        for (Class<?> type : COMPILED) {
            if (OPEN.contains(type)) {
                continue;
            }
            // A record's components are its fields, so it is read one way or the other and never
            // both: a value named twice reads as two values holding the pair.
            for (String held : heldBy(type)) {
                holding.add(held);
            }
        }
        assertEquals(List.of(), holding,
                "holding both is two answers to one question with nothing keeping them the same,"
                        + " which is what #760 was. Read the source off the place, or say why the"
                        + " two are different questions — a value that has a scope and, separately,"
                        + " a place is not this defect, and what admits one is a component that"
                        + " says so");
    }

    /**
     * And nothing hands the two over separately either.
     *
     * <p>Asked of constructors and of static factories, because the pair reached a label through
     * {@code secondaryIn(String, Region, Message)} as readily as through a constructor, and a check
     * that read constructors alone would let that entry back in without noticing.
     */
    @Test
    void nothingTakesASourceIdentityBesideAPlaceThatAnswersForOne() {
        List<String> taking = new ArrayList<>();
        for (Class<?> type : COMPILED) {
            if (OPEN.contains(type)) {
                continue;
            }
            for (Constructor<?> made : type.getDeclaredConstructors()) {
                if (Modifier.isPublic(made.getModifiers()) && takesBoth(made)) {
                    taking.add(made.toGenericString());
                }
            }
            for (Method called : type.getDeclaredMethods()) {
                if (Modifier.isPublic(called.getModifiers()) && takesBoth(called)) {
                    taking.add(called.toGenericString());
                }
            }
        }
        assertEquals(List.of(), taking,
                "a site handing over a source and a place separately is a marker in one file with"
                        + " its line read from another");
    }

    /** The scan reaches what it claims to. A check that quietly loaded nothing would pass whatever
     *  the code did, so this holds it to seeing the values this rule was written about. */
    @Test
    void theScanReachesTheValuesThisRuleIsAbout() {
        assertTrue(COMPILED.size() > 500, "the compiler and its syntax, not a handful: " + COMPILED.size());
        for (Class<?> named : List.of(SourcePos.class, Region.class, Citation.class,
                Spot.InSource.class, Spot.InTextBeingRead.class, Diagnostic.class, Located.class,
                souther.compiler.query.Db.Found.class,
                DiagnosticPlace.InSource.class, souther.compiler.observe.RowOutcome.class,
                souther.compiler.observe.Incompleteness.class,
                souther.compiler.query.Output.Examples.class)) {
            assertTrue(COMPILED.contains(named), named + " is not among what was read");
        }
        assertFalse(OPEN.stream().anyMatch(open -> !COMPILED.contains(open)),
                "an open case nothing reads is an exception to nothing");
    }

    /** What this type holds a source identity as, where it also holds a place that answers for
     *  one. Empty for everything else. */
    private static List<String> heldBy(Class<?> type) {
        List<String> held = new ArrayList<>();
        if (!holdsAPlace(type)) {
            return held;
        }
        if (type.isRecord()) {
            for (RecordComponent c : componentsOf(type)) {
                if (mentions(c.getGenericType(), SourceId.class)) {
                    held.add(type.getName() + "." + c.getName());
                }
            }
            return held;
        }
        for (Field f : type.getDeclaredFields()) {
            if (!Modifier.isStatic(f.getModifiers()) && mentions(f.getGenericType(), SourceId.class)) {
                held.add(type.getName() + "." + f.getName());
            }
        }
        return held;
    }

    /**
     * Whether {@code held} is {@code wanted}, or a container of it.
     *
     * <p>Read through the wrapping, because the shape this rule is about wore some. The field this
     * change removed was {@code Optional<SourceRef>}, and a check that compared the erased type
     * would have watched it go and said nothing when it came back as {@code Optional<SourceId>} — a
     * guard that is green for the very value it was written about.
     */
    private static boolean mentions(Type held, Class<?> wanted) {
        if (held instanceof Class<?> c) {
            return wanted.isAssignableFrom(c)
                    || c.isArray() && mentions(c.getComponentType(), wanted);
        }
        if (held instanceof GenericArrayType array) {
            return mentions(array.getGenericComponentType(), wanted);
        }
        if (held instanceof ParameterizedType parameterized) {
            if (mentions(parameterized.getRawType(), wanted)) {
                return true;
            }
            for (Type argument : parameterized.getActualTypeArguments()) {
                if (mentions(argument, wanted)) {
                    return true;
                }
            }
        }
        return false;
    }

    private static boolean mentionsAPlace(Type held) {
        return ANSWERS_FOR_A_SOURCE.stream().anyMatch(place -> mentions(held, place));
    }

    private static boolean holdsAPlace(Class<?> type) {
        if (type.isRecord()) {
            for (RecordComponent c : componentsOf(type)) {
                if (mentionsAPlace(c.getGenericType())) {
                    return true;
                }
            }
            return false;
        }
        for (Field f : type.getDeclaredFields()) {
            if (!Modifier.isStatic(f.getModifiers()) && mentionsAPlace(f.getGenericType())) {
                return true;
            }
        }
        return false;
    }

    private static RecordComponent[] componentsOf(Class<?> type) {
        RecordComponent[] components = type.getRecordComponents();
        return components == null ? new RecordComponent[0] : components;
    }

    private static boolean takesBoth(Executable made) {
        boolean names = false;
        boolean carries = false;
        for (Parameter p : made.getParameters()) {
            names |= mentions(p.getParameterizedType(), SourceId.class);
            carries |= mentionsAPlace(p.getParameterizedType());
        }
        return names && carries;
    }

    /**
     * Every class this module and the syntax module compiled, read off the class path rather than
     * listed.
     *
     * <p>Both shapes a module arrives in. A reactor build puts one module's classes in a directory
     * and another's in a jar, and a scan that read only directories saw whichever half the command
     * happened to build from source — which is a scan that passes by seeing nothing. What holds it
     * to seeing both is {@link #theScanReachesTheValuesThisRuleIsAbout}, which is how that was
     * found.
     *
     * <p>Not initialised: a class is loaded for what it declares, and running its static
     * initialisers would make this test depend on what they touch.
     */
    private static List<Class<?>> compiled() {
        List<Class<?>> found = new ArrayList<>();
        for (String entry : System.getProperty("java.class.path").split(java.io.File.pathSeparator)) {
            if (!entry.contains("souther-")) {
                continue;
            }
            Path root = Path.of(entry);
            if (Files.isDirectory(root)) {
                try (Stream<Path> walk = Files.walk(root)) {
                    walk.filter(each -> each.toString().endsWith(".class"))
                            .map(each -> root.relativize(each).toString())
                            .forEach(name -> load(name, found));
                } catch (IOException e) {
                    throw new UncheckedIOException(e);
                }
            } else if (entry.endsWith(".jar") && Files.isRegularFile(root)) {
                try (java.util.jar.JarFile jar = new java.util.jar.JarFile(root.toFile())) {
                    jar.stream().map(java.util.zip.ZipEntry::getName)
                            .filter(name -> name.endsWith(".class"))
                            .forEach(name -> load(name, found));
                } catch (IOException e) {
                    throw new UncheckedIOException(e);
                }
            }
        }
        return List.copyOf(found);
    }

    private static void load(String path, List<Class<?>> into) {
        String name = path.substring(0, path.length() - ".class".length())
                .replace(java.io.File.separatorChar, '.').replace('/', '.');
        if (!name.startsWith("souther.") || name.endsWith("package-info")
                || name.endsWith("module-info")) {
            return;
        }
        try {
            into.add(Class.forName(name, false,
                    NoValueHoldsASourceBesideOneThatAnswersForItTest.class.getClassLoader()));
        } catch (ClassNotFoundException | LinkageError _) {
            // a class this test's path cannot resolve says nothing about the rule
        }
    }
}
