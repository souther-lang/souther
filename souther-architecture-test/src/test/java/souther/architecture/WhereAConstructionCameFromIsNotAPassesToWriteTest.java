package souther.architecture;

import souther.compiler.ast.Ast;
import souther.compiler.ast.Hir;
import souther.test.RepositoryLayout;

import org.junit.jupiter.api.Test;

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
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
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
 * the population is whole is asserted against {@link RepositoryLayout}, which is what says what the
 * repository is made of: a module added without a dependency from here would otherwise be passed
 * over in silence.
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

    /** Every module of the repository is read, which is what makes the answer above about all of
     *  them. The modules are {@link RepositoryLayout}'s, so one added without a dependency from
     *  here is a failure rather than a gap. */
    @Test
    void andEveryModuleTheRepositoryHoldsIsInWhatWasRead() {
        Set<String> read = new LinkedHashSet<>();
        for (Path each : everyCompiledClass()) {
            read.add(REPOSITORY.root().relativize(each).getName(0).toString());
        }

        assertEquals(everyModule(), read,
                "a module whose classes were not built when this ran is one this says nothing"
                        + " about. Every module is depended on from here so that Maven builds it"
                        + " first");
    }

    /** The control: the walk sees the reference where the forms themselves make it. */
    @Test
    void andTheCheckSeesTheReferenceWhereItIsAllowed() {
        Set<String> forms = formsThatHoldAnOrigin();

        assertEquals(Set.of(THEIRS + "Hir$NewData", THEIRS + "Hir$Apply"), forms,
                "the forms are read off the tree, and these are the two");
        assertTrue(everyCompiledClass().stream()
                        .filter(each -> internalName(each).equals(THEIRS + "Hir$Apply"))
                        .anyMatch(each -> handsAnOriginTo(forms, each)),
                "the form itself hands an origin to its own constructor, which is what this reads");
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
