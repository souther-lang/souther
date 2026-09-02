package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.check.Derived;
import souther.compiler.check.Registry;
import souther.compiler.meta.ModulePath;
import souther.compiler.types.TypeKey;

import java.io.File;
import java.io.IOException;
import java.io.UncheckedIOException;
import java.lang.reflect.GenericArrayType;
import java.lang.reflect.MalformedParameterizedTypeException;
import java.lang.reflect.Method;
import java.lang.reflect.ParameterizedType;
import java.lang.reflect.Type;
import java.lang.reflect.TypeVariable;
import java.lang.reflect.WildcardType;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.jar.JarFile;
import java.util.stream.Stream;
import java.util.zip.ZipEntry;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the derivation answered for is handed on as what it answered for.
 *
 * <p>One declaration may be read for what resolution left of it — its fields, what it includes,
 * whether it is a newtype, all of which mean the same thing whichever stage is asking. A whole table
 * may not. Turned back into nodes, every declaration below the stage arrives with nothing left
 * saying it came out, and a reader that needed the boundary representation is holding a declaration
 * that cannot tell it there is none.
 *
 * <p>The two halves are held apart here: the table the compilation's declarations are read through
 * says which stage they are at, and nothing carries a table across.
 */
class ATableOfDerivedDeclarationsIsNeverReadBackAsNodesTest {

    /** The registry a reader below the derivation is answered from hands over derived
     *  declarations. */
    @Test
    void theDerivedRegistryHandsOverDerivedDeclarations() throws NoSuchMethodException {
        Method registry = Names.class.getDeclaredMethod("derivedRegistry", Db.class);

        assertEquals(Registry.class, registry.getReturnType());
        assertEquals(List.of(Derived.Def.class), heldBy(registry.getGenericReturnType()),
                "the derived registry answers with something other than a derived declaration");
    }

    /** And the resolved one with declarations as resolution left them, which is the other world and
     *  not a projection of this one. */
    @Test
    void theResolvedRegistryHandsOverNodes() throws NoSuchMethodException {
        Method registry = Names.class.getDeclaredMethod("resolvedRegistry", Db.class);

        assertEquals(List.of(Hir.Def.class), heldBy(registry.getGenericReturnType()));
    }

    /**
     * Nothing anywhere turns a table of derived declarations into a table of nodes.
     *
     * <p>Read of the signatures rather than of what a body does, because the shape is what a later
     * change reaches for: a method handed the derived declarations and answering with the nodes is
     * how the stage came to be thrown away the first time, and it reads as a convenience until
     * somebody asks what the reader on the far side of it is holding.
     *
     * <p>Over every class this compiler is made of. Asked of the few that hold one today, the rule
     * would be about the places the stage already reaches and say nothing about the next method
     * somewhere else that takes the table — which is the only way one gets written.
     */
    @Test
    void nothingCarriesATableOfThemAcross() {
        List<String> carrying = new ArrayList<>();
        for (Class<?> each : COMPILED) {
            for (Method m : declaredMethodsOf(each)) {
                boolean takesDerived = false;
                Type answers;
                try {
                    for (Type parameter : m.getGenericParameterTypes()) {
                        takesDerived |= heldBy(parameter).contains(Derived.Def.class);
                    }
                    answers = m.getGenericReturnType();
                } catch (TypeNotPresentException | MalformedParameterizedTypeException
                        | LinkageError _) {
                    continue;   // a signature this test's path cannot read says nothing either way
                }
                if (takesDerived && heldBy(answers).contains(Hir.Def.class)) {
                    carrying.add(each.getName() + "." + m.getName());
                }
            }
        }
        assertEquals(List.of(), carrying,
                "a table of derived declarations is read back as a table of nodes");
    }

    /**
     * And the scan reaches the classes this rule is about.
     *
     * <p>A walk that resolved nothing would report no method carrying a table, which is a rule that
     * passes by seeing nothing. Held to the classes that hand the table around, since those are the
     * ones a violation would be written in.
     */
    @Test
    void theScanReachesTheClassesThatHoldTheTable() {
        for (Class<?> each : List.of(Names.class, Shapes.class, Derived.class,
                souther.compiler.check.DerivedSymbols.class,
                souther.compiler.check.Declarations.class)) {
            assertTrue(COMPILED.contains(each), each.getName() + " is not in what was scanned");
        }
        assertTrue(COMPILED.size() > 500,
                "the scan found " + COMPILED.size() + " classes, which is not this compiler");
    }

    /** What a class declares, or nothing where this test's path cannot resolve a signature — a
     *  class whose types are not all here says nothing about the rule either way. */
    private static List<Method> declaredMethodsOf(Class<?> each) {
        try {
            return List.of(each.getDeclaredMethods());
        } catch (LinkageError _) {
            return List.of();
        }
    }

    /**
     * A declaration nobody could derive is one no reader is told is settled.
     *
     * <p>One direction and not the other. A declaration that did not come out has no definition to
     * name, which is what a reader that filters on one and reads through the other rests on; a
     * declaration comes out while the module around it has names that answer nothing, so the
     * derivation's own refusal is not a gate something else could take over.
     *
     * <p>Two declarations rather than a population, because what is held here is the direction. A
     * count of how often each way round holds is a measurement over a compile and is written where
     * the measurement was made.
     */
    @Test
    void aDeclarationThatDidNotComeOutIsNotSettledEither() {
        Compilation compilation = Compilation.ofSources(List.of("""
                module probe.holes exposing ( Bad, Good )

                data Bad = { value: Nowhere }
                data Good = { n: Int }
                """), ModulePath.EMPTY);
        Db db = compilation.db();

        TypeKey bad = new TypeKey("probe.holes", "Bad");
        TypeKey good = new TypeKey("probe.holes", "Good");

        assertFalse(db.ask(new Shapes.DerivedDef(bad)).present(),
                "`Bad` holds a field naming nothing, so nothing derived it");
        assertFalse(db.ask(new Names.Definition(bad)).present(),
                "and nothing says it is settled either");
        assertTrue(db.ask(new Shapes.DerivedDef(good)).present(),
                "`Good` came out");
        assertTrue(db.ask(new Names.Definition(good)).present(),
                "and is settled");
    }

    /**
     * What a type holds, as the classes named in its arguments.
     *
     * <p>Through what stands for a class as well as through a class written out. A bound
     * ({@code Registry<? extends Derived.Def>}) and a variable declared over one
     * ({@code <D extends Derived.Def> Map<String, D>}) name the same declarations the written class
     * does, and a reading that took only the classes would let either of them past — the erasure of
     * both is {@code Object}, so nothing about them says what they carry.
     */
    private static List<Class<?>> heldBy(Type type) {
        List<Class<?>> out = new ArrayList<>();
        heldBy(type, new HashSet<>(), out);
        return out;
    }

    /**
     * The same, over a type already being read.
     *
     * <p>{@code seen} because a variable may be bounded by something written in terms of itself
     * ({@code <T extends Comparable<T>>}), and a walk with nothing to stop it follows that bound
     * back to the variable for as long as the stack lasts.
     */
    private static void heldBy(Type type, Set<Type> seen, List<Class<?>> out) {
        if (!seen.add(type)) {
            return;
        }
        switch (type) {
            case ParameterizedType parameterized -> {
                for (Type argument : parameterized.getActualTypeArguments()) {
                    if (argument instanceof Class<?> named) {
                        out.add(named);
                    } else {
                        heldBy(argument, seen, out);
                    }
                }
            }
            case WildcardType wildcard -> {
                namedIn(wildcard.getUpperBounds(), seen, out);
                namedIn(wildcard.getLowerBounds(), seen, out);
            }
            case TypeVariable<?> variable -> namedIn(variable.getBounds(), seen, out);
            case GenericArrayType array -> heldBy(array.getGenericComponentType(), seen, out);
            default -> { }
        }
    }

    /** The classes among a set of bounds, and what those bounds themselves hold. {@code Object} is
     *  what an unbounded one says, which is nothing about this rule. */
    private static void namedIn(Type[] bounds, Set<Type> seen, List<Class<?>> out) {
        for (Type bound : bounds) {
            if (bound instanceof Class<?> named) {
                if (named != Object.class) {
                    out.add(named);
                }
            } else {
                heldBy(bound, seen, out);
            }
        }
    }

    /**
     * Every class this compiler is made of, loaded and not initialised.
     *
     * <p>Both shapes a module arrives in: a reactor build puts one module's classes in a directory
     * and another's in a jar, so a scan reading only directories sees whichever half the command
     * built from source. What holds it to seeing both is
     * {@link #theScanReachesTheClassesThatHoldTheTable}.
     */
    private static final List<Class<?>> COMPILED = compiled();

    private static List<Class<?>> compiled() {
        List<Class<?>> found = new ArrayList<>();
        for (String entry : System.getProperty("java.class.path").split(File.pathSeparator)) {
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
                try (JarFile jar = new JarFile(root.toFile())) {
                    jar.stream().map(ZipEntry::getName)
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
                .replace(File.separatorChar, '.').replace('/', '.');
        if (!name.startsWith("souther.") || name.endsWith("package-info")
                || name.endsWith("module-info")) {
            return;
        }
        try {
            into.add(Class.forName(name, false,
                    ATableOfDerivedDeclarationsIsNeverReadBackAsNodesTest.class.getClassLoader()));
        } catch (ClassNotFoundException | LinkageError _) {
            // a class this test's path cannot resolve says nothing about the rule
        }
    }
}
