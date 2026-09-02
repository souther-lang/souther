package souther.architecture;

import souther.compiler.ast.Ast;
import souther.compiler.ast.Hir;
import souther.test.RepositoryLayout;

import org.junit.jupiter.api.Test;

import java.io.File;
import java.io.IOException;
import java.io.UncheckedIOException;
import java.lang.classfile.ClassFile;
import java.lang.classfile.constantpool.MemberRefEntry;
import java.lang.classfile.constantpool.PoolEntry;
import java.lang.reflect.RecordComponent;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A construction says where it came from, and no pass says it for one.
 *
 * <p>The arms of a construction origin are declared where only {@code souther.compiler.ast} can name
 * them, so a pass elsewhere cannot make one or ask one what it means. What javac cannot refuse is a
 * pass taking an origin off a node and handing it to another node, which is the same defect a step
 * along: the answer would come from wherever the writer happened to have one rather than from what
 * the node is. So the forms are built through the constructors that take no origin, and a member
 * that takes one is this package's to call.
 *
 * <p>Read off the compiled classes and not the source, because it is a rule about who calls what: a
 * reference is in the constant pool of the class that makes it whatever the call looks like.
 *
 * <p>Both sets it works from are read off the tree rather than written here. The forms it watches
 * are the ones whose components say where a construction came from, so a third form that holds one
 * is watched the day it is written; and the members it forbids are every member of those forms whose
 * descriptor takes an origin, so a second way in beside the constructor is forbidden the day it is
 * declared. A check that spelled either set would go on saying what it said while the thing it is
 * about moved.
 *
 * <p>This lives in a module that depends on every other, so every module's classes are built when it
 * runs and the population is the whole repository rather than whatever happened to be built. That
 * every module is depended on is asserted below against {@link RepositoryLayout}, which is what says
 * what the repository is made of — a module added without a dependency from here would otherwise be
 * passed over in silence, and the build order does not reliably show it.
 *
 * <p>Which forms hold an origin, and that they are the two, is the compiler's own to say and is
 * said in its tests. What is here is the question no module can answer alone: who, across every
 * module of the reactor, calls what.
 */
class WhereAConstructionCameFromIsNotAPassesToWriteTest {

    private static final String ORIGIN = "Lsouther/compiler/ast/ConstructionOrigin;";

    /** Where the forms are written, and so where an origin may be handed to one. */
    private static final String THEIRS = "souther/compiler/ast/";

    private static final RepositoryLayout REPOSITORY = RepositoryLayout.ofWorkingDirectory();

    @Test
    void nothingOutsideTheTreeWritesAnOriginIntoAConstruction() {
        Set<String> forms = formsThatHoldAnOrigin();

        List<String> writing = new ArrayList<>();
        for (Path each : everyCompiledClass()) {
            if (internalName(each).startsWith(THEIRS) || !handsAnOriginTo(forms, each)) {
                continue;
            }
            writing.add(internalName(each));
        }

        assertEquals(List.of(), writing.stream().sorted().toList(),
                "a pass writing one of these forms says what it is building and not where the"
                        + " construction came from: the constructors that take no origin are the"
                        + " ones to call, and a rebuild carries the origin it was handed");
    }

    /**
     * Every module of the repository is depended on from here, which is what has them built when
     * this runs and so what makes the answer above about all of them.
     *
     * <p>Asked of the classpath these tests run on, which Maven builds from the dependencies this
     * module declares: a module missing from it is a module this build had no reason to compile
     * before running these, and what the walk would find of it is whatever an earlier build left.
     *
     * <p>Not asked of the build order. A module is built before this one because something depends
     * on it, and a dependency left out is only sometimes visible there: what sends this module to
     * the end is every edge it has, so an omitted edge is covered whenever another module it does
     * depend on is written after the one it forgot. Measured — dropping the dependency on
     * {@code souther-cli} left the build order unchanged.
     */
    @Test
    void andEveryModuleTheRepositoryHoldsIsDependedOnFromHere() {
        Set<String> built = new TreeSet<>();
        for (String entry : System.getProperty("java.class.path").split(File.pathSeparator)) {
            Path where = Path.of(entry);
            if (where.endsWith(Path.of("target", "classes")) && where.startsWith(REPOSITORY.root())) {
                built.add(where.getParent().getParent().getFileName().toString());
            }
        }

        assertEquals(new TreeSet<>(everyModule()), built,
                "a module this does not depend on is one nothing has built when this runs, and one"
                        + " this then says nothing about");
    }

    /** The control: the walk found forms to watch and sees the reference where they make it
     *  themselves. Which forms those are is the compiler's own to say, and its tests do. */
    @Test
    void andTheCheckSeesTheReferenceWhereItIsAllowed() {
        Set<String> forms = formsThatHoldAnOrigin();

        assertFalse(forms.isEmpty(), "a form that holds an origin is what this watches");
        assertTrue(everyCompiledClass().stream()
                        .filter(each -> forms.contains(internalName(each)))
                        .anyMatch(each -> handsAnOriginTo(forms, each)),
                "a form hands an origin to its own constructor, which is what this reads");
    }

    /** The forms that say where a construction came from, read off the trees that have them. */
    private static Set<String> formsThatHoldAnOrigin() {
        Set<String> holders = new LinkedHashSet<>();
        for (Class<?> tree : List.of(Ast.class, Hir.class)) {
            for (Class<?> form : tree.getNestMembers()) {
                if (!form.isRecord()) {
                    continue;
                }
                for (RecordComponent part : form.getRecordComponents()) {
                    if (part.getType().getName().equals("souther.compiler.ast.ConstructionOrigin")) {
                        holders.add(form.getName().replace('.', '/'));
                    }
                }
            }
        }
        return holders;
    }

    /** Whether {@code compiled} names a member of one of {@code forms} that takes an origin. */
    private static boolean handsAnOriginTo(Set<String> forms, Path compiled) {
        try {
            for (PoolEntry entry : ClassFile.of().parse(Files.readAllBytes(compiled))
                    .constantPool()) {
                if (entry instanceof MemberRefEntry member
                        && forms.contains(member.owner().name().stringValue())
                        && takesAnOrigin(member.type().stringValue())) {
                    return true;
                }
            }
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
        return false;
    }

    /** Whether a descriptor takes an origin, which is what a member may not be handed from outside.
     *  What it answers with is another question: a form holds one and says so. */
    private static boolean takesAnOrigin(String descriptor) {
        int arguments = descriptor.lastIndexOf(')');
        return arguments > 0 && descriptor.substring(0, arguments).contains(ORIGIN);
    }

    /** The class's own binary name, read off the file's place under its module's build directory. */
    private static String internalName(Path compiled) {
        String path = compiled.toString().replace('\\', '/');
        int at = path.indexOf("/classes/");
        int from = at < 0 ? path.indexOf("/test-classes/") + "/test-classes/".length()
                : at + "/classes/".length();
        return path.substring(from, path.length() - ".class".length());
    }

    /** Every class of every module of this build, main and test alike. */
    private static List<Path> everyCompiledClass() {
        List<Path> out = new ArrayList<>();
        for (Path module : REPOSITORY.modules()) {
            for (String built : List.of("classes", "test-classes")) {
                Path where = module.resolve("target").resolve(built);
                if (!Files.isDirectory(where)) {
                    continue;
                }
                try (Stream<Path> found = Files.walk(where)) {
                    out.addAll(found.filter(p -> p.toString().endsWith(".class")).toList());
                } catch (IOException e) {
                    throw new UncheckedIOException(e);
                }
            }
        }
        return out;
    }

    /** What the repository's modules are called, which is {@link RepositoryLayout}'s answer and not
     *  a second reading of the root pom. */
    private static Set<String> everyModule() {
        return REPOSITORY.modules().stream().map(each -> each.getFileName().toString())
                .collect(java.util.stream.Collectors.toCollection(LinkedHashSet::new));
    }
}
