package souther.architecture;

import souther.compiler.types.CoverageConstruct;
import souther.compiler.types.CoverageOrigin;
import souther.test.RepositoryLayout;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.lang.classfile.ClassFile;
import java.lang.classfile.constantpool.MemberRefEntry;
import java.lang.classfile.constantpool.PoolEntry;
import java.lang.reflect.Constructor;
import java.lang.reflect.Method;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Who may say which construct a coverage obligation was written as.
 *
 * <p>A non-recursive helper is expanded at each call, so one construct the author wrote becomes
 * several in the tree that runs, and what says those copies are one obligation is that they carry
 * one origin. An origin made after that expansion gives two copies of one construct two, which is
 * the thing the type exists to prevent. Its own account says where one may be made: at the reading
 * of a source construct, at a rewrite that reads a call back as the comparison it means and has no
 * source to answer for, and at the derivation of the forks a lowering makes.
 *
 * <p>Nothing held that. The record's constructor is public and takes every component, as a record's
 * is, so a pass reaching for one makes whatever it likes. So the account is read off the compiled
 * classes here: every class naming a member that makes an origin, with the member it names.
 *
 * <p>What is read is the constant pool and not the instructions. A name reached through a method
 * reference is a constant and no call instruction — {@code CoverageOrigin::unwritten} handed to
 * something that will call it makes an origin as surely as calling it here does, and a walk over
 * instructions passes over it.
 *
 * <p>Not the shape its neighbours have. Where a construction came from and which of its fields had
 * to be written are answered by asking the node, so their vocabulary stays inside the package that
 * owns it and a check over callers is enough. What reads a coverage origin reads the module, the
 * construct and the fork, so the vocabulary crosses and who names the makers is what there is to
 * read.
 *
 * <p>A member that hands on an origin it was given is not one of these. {@link
 * souther.compiler.ast.Hir.ListComp#forkOfGuard} derives a fork by asking the origin it holds, and
 * what it can answer with is a fork of its own comprehension and nothing else — which is that
 * method's to refuse and is refused there, rather than a thing this could tell by reading a call.
 */
class WhoMaySettleACoverageOriginTest {

    /** Read off the type, so that renaming it stops the build rather than leaving this walk with
     *  nothing to find and nothing to say. */
    private static final String OWNER = internalNameOf(CoverageOrigin.class);

    private static final String AN_ORIGIN = "L" + OWNER + ";";

    private static final String A_CONSTRUCT = "L" + internalNameOf(CoverageConstruct.class) + ";";

    private static final RepositoryLayout REPOSITORY = RepositoryLayout.ofWorkingDirectory();

    /**
     * What makes an origin, written down — so that a way of making one that is added is a row here
     * before anyone names it, and not a silence until someone does.
     */
    private static final List<String> MAKERS = List.of(
            OWNER + "#<init>(Ljava/lang/String;II" + A_CONSTRUCT + ")V",
            OWNER + "#lowered(I)" + AN_ORIGIN,
            OWNER + "#unwritten()" + AN_ORIGIN,
            OWNER + "#written(Ljava/lang/String;I" + A_CONSTRUCT + ")" + AN_ORIGIN);

    /**
     * Every class that names one of the makers, with the maker it names.
     *
     * <p>A source construct is read in one place. {@code TheOtherCase}, {@code Terms} and
     * {@code Conditions} read a preserved call back as the comparison it means, and a preserved call
     * holds no origin, so there is none to carry and each says which it is answering. The fork of a
     * comprehension's guard is derived where the comprehension is, so that the lowering and the
     * reading that runs before it cannot number the guards differently.
     *
     * <p>{@code Hir.Apply} and {@code Elaborator} are the two places an application stands where no
     * source wrote one. A pass composing an application is writing one into a body, and a name read
     * where a value goes is built as a call of no arguments — an author wrote a name there, not an
     * application. Each says so rather than taking the number of a construct somebody wrote, which
     * after an expansion is this compiler's own work standing among the model's.
     *
     * <p>The constructor is named only from inside {@code CoverageOrigin}. A row naming it elsewhere
     * is a pass making an origin of its own, which after an expansion is two obligations where the
     * author wrote one.
     */
    private static final List<String> NAMING_A_MAKER = List.of(
            "souther/compiler/ast/Hir$Apply -> " + OWNER + "#unwritten()" + AN_ORIGIN,
            "souther/compiler/ast/Hir$ListComp -> " + OWNER + "#lowered(I)" + AN_ORIGIN,
            "souther/compiler/check/Conditions -> " + OWNER + "#unwritten()" + AN_ORIGIN,
            "souther/compiler/check/Conditions$AsPolar -> " + OWNER + "#unwritten()" + AN_ORIGIN,
            "souther/compiler/check/Elaborator -> " + OWNER + "#unwritten()" + AN_ORIGIN,
            "souther/compiler/check/Terms -> " + OWNER + "#unwritten()" + AN_ORIGIN,
            "souther/compiler/check/TheOtherCase -> " + OWNER + "#unwritten()" + AN_ORIGIN,
            "souther/compiler/frontend/AstBuilder -> " + OWNER
                    + "#written(Ljava/lang/String;I" + A_CONSTRUCT + ")" + AN_ORIGIN,
            OWNER + " -> " + OWNER + "#<init>(Ljava/lang/String;II" + A_CONSTRUCT + ")V");

    @Test
    void everyWayOfMakingOneIsWrittenDown() {
        assertEquals(MAKERS, new ArrayList<>(makers()),
                "a row added here is a way to say which construct an obligation was written as:"
                        + " say what reads a source to answer it, and add who names it");
    }

    @Test
    void andEveryClassThatNamesOneIsWrittenDownWithWhatItNames() {
        assertEquals(NAMING_A_MAKER, new ArrayList<>(namingAMaker()),
                "an origin is made where a source is read and where a rewrite has no source to"
                        + " answer for, and derived where a lowering forks one construct into"
                        + " several: a row that is neither is a copy given an obligation of its own");
    }

    /**
     * The walk reads every module's classes.
     *
     * <p>Asked of the modules the repository has and not of what a build happened to leave: a module
     * whose classes are missing is one whose calls this cannot see, and the rows from the rest would
     * match and this would pass while answering about fewer modules than it names.
     */
    @Test
    void andEveryModuleTheRepositoryHoldsWasRead() {
        List<String> unbuilt = new ArrayList<>();
        for (Path module : REPOSITORY.modules()) {
            if (!Files.isDirectory(classesOf(module)) && hasMainSources(module)) {
                unbuilt.add(module.getFileName().toString());
            }
        }

        assertEquals(List.of(), unbuilt,
                "a module whose classes are not built is one this walk passes over, and a walk that"
                        + " passes over a module answers about the rest while saying it answers"
                        + " about all of them");
        assertTrue(modulesRead() > 1,
                "the classes this reads are in more than the one module that declares an origin");
    }

    /** Every member of {@code CoverageOrigin} that answers with one, and the constructor they all go
     *  through — read off the type rather than written out, so a member added beside them is one of
     *  these by being one. */
    private static Set<String> makers() {
        Set<String> members = new TreeSet<>();
        for (Method each : CoverageOrigin.class.getDeclaredMethods()) {
            if (each.getReturnType() == CoverageOrigin.class) {
                members.add(OWNER + "#" + each.getName()
                        + descriptorOf(each.getParameterTypes(), each.getReturnType()));
            }
        }
        for (Constructor<?> each : CoverageOrigin.class.getDeclaredConstructors()) {
            members.add(OWNER + "#<init>" + descriptorOf(each.getParameterTypes(), void.class));
        }
        return members;
    }

    /** Every class naming a maker, as the class and the maker — the maker by the whole of what it
     *  is, as the key that found it was. */
    private static Set<String> namingAMaker() {
        Set<String> found = new TreeSet<>();
        Set<String> makers = makers();
        for (Path module : REPOSITORY.modules()) {
            for (Path each : classesUnder(module)) {
                for (PoolEntry entry : constantPoolOf(each)) {
                    if (entry instanceof MemberRefEntry member) {
                        String named = member.owner().name().stringValue() + "#"
                                + member.name().stringValue() + member.type().stringValue();
                        if (makers.contains(named)) {
                            found.add(internalName(module, each) + " -> " + named);
                        }
                    }
                }
            }
        }
        return found;
    }

    private static int modulesRead() {
        int read = 0;
        for (Path module : REPOSITORY.modules()) {
            if (!classesUnder(module).isEmpty()) {
                read++;
            }
        }
        return read;
    }

    private static Iterable<PoolEntry> constantPoolOf(Path compiled) {
        try {
            return ClassFile.of().parse(Files.readAllBytes(compiled)).constantPool();
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    /** The class's own binary name, taken against the directory it was found under rather than off
     *  the first {@code classes} in the path, which a checkout under one would be. */
    private static String internalName(Path module, Path compiled) {
        String name = classesOf(module).relativize(compiled).toString().replace('\\', '/');
        return name.substring(0, name.length() - ".class".length());
    }

    private static Path classesOf(Path module) {
        return module.resolve("target").resolve("classes");
    }

    /** Whether the module has main sources to have been built from. A module holding only tests or
     *  only a pom leaves no classes and is not one this walk is missing. */
    private static boolean hasMainSources(Path module) {
        return Files.isDirectory(module.resolve("src").resolve("main").resolve("java"));
    }

    /** The compiled classes of one module that the compiler is made of. Its own tests are not among
     *  them: a test builds an origin to look at it and ships nothing, and a list that moved whenever
     *  one was written is a list nobody keeps up. */
    private static List<Path> classesUnder(Path module) {
        Path where = classesOf(module);
        if (!Files.isDirectory(where)) {
            return List.of();
        }
        try (Stream<Path> found = Files.walk(where)) {
            return found.filter(p -> p.toString().endsWith(".class")).toList();
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    /** The descriptor of a member taking these and answering with that. */
    private static String descriptorOf(Class<?>[] takes, Class<?> answers) {
        StringBuilder out = new StringBuilder("(");
        for (Class<?> each : takes) {
            out.append(descriptorOf(each));
        }
        return out.append(')').append(descriptorOf(answers)).toString();
    }

    private static String descriptorOf(Class<?> type) {
        if (type == void.class) {
            return "V";
        }
        if (type == int.class) {
            return "I";
        }
        if (type == boolean.class) {
            return "Z";
        }
        if (type.isArray()) {
            return "[" + descriptorOf(type.getComponentType());
        }
        return "L" + internalNameOf(type) + ";";
    }

    private static String internalNameOf(Class<?> type) {
        return type.getName().replace('.', '/');
    }
}
