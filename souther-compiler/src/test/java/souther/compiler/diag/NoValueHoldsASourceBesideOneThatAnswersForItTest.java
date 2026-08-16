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
import java.lang.reflect.RecordComponent;
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
 * <p>The rule is written on {@link WrittenAt}: <em>a source location has exactly one authority for
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
 * <h2>What it does not reach</h2>
 *
 * <p>The classes on this test's path, which is this module's and the syntax module's. An editor and
 * a command line hold sources of their own under names of their own, and neither is here.
 */
class NoValueHoldsASourceBesideOneThatAnswersForItTest {

    /** The types that answer for a source of their own, so holding one beside them is holding two
     *  answers to one question. */
    private static final Set<Class<?>> ANSWERS_FOR_A_SOURCE = Set.of(
            Region.class, SourcePos.class, DiagnosticPlace.InSource.class,
            Citation.class, Citation.Written.class, Citation.OutOfSight.class);

    /**
     * The one value that holds both, and it is an open question rather than a shape this rule does
     * not cover.
     *
     * <p>{@link Spot} pairs a told source with a region, and the reason is not that a primary is a
     * different kind of place. A secondary is built through {@link DiagnosticPlace}, so it names a
     * source by construction; a primary is not held to that, and over one compile of this suite 53
     * of 3545 diagnostics carried a primary region that names no source while saying the code is
     * written at it, with another 22 carrying no region at all. Where the region does not answer,
     * the told source is the only answer there is.
     *
     * <p>So what is unsettled is not whether the pair may exist but what the second half means: the
     * source the region is in, or the file this report is being read from. Deciding that means
     * reading what those 53 diagnostics are about, across the fourteen codes they came from, and
     * that is a question about the diagnostic model rather than about source identity. Named here so
     * that it goes when that question is answered, rather than outliving it as a rule nobody
     * remembers writing.
     */
    private static final Set<Class<?>> OPEN = Set.of(Spot.class);

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
        for (Class<?> named : List.of(SourcePos.class, Region.class, Citation.class, Spot.class,
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
                if (c.getType() == SourceId.class) {
                    held.add(type.getName() + "." + c.getName());
                }
            }
            return held;
        }
        for (Field f : type.getDeclaredFields()) {
            if (!Modifier.isStatic(f.getModifiers()) && f.getType() == SourceId.class) {
                held.add(type.getName() + "." + f.getName());
            }
        }
        return held;
    }

    private static boolean holdsAPlace(Class<?> type) {
        if (type.isRecord()) {
            for (RecordComponent c : componentsOf(type)) {
                if (ANSWERS_FOR_A_SOURCE.contains(c.getType())) {
                    return true;
                }
            }
            return false;
        }
        for (Field f : type.getDeclaredFields()) {
            if (!Modifier.isStatic(f.getModifiers()) && ANSWERS_FOR_A_SOURCE.contains(f.getType())) {
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
            names |= p.getType() == SourceId.class;
            carries |= ANSWERS_FOR_A_SOURCE.contains(p.getType());
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
