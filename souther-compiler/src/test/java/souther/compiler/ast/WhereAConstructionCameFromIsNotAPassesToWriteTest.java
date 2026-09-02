package souther.compiler.ast;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.lang.classfile.ClassFile;
import java.lang.classfile.constantpool.MemberRefEntry;
import java.lang.classfile.constantpool.PoolEntry;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A construction says where it came from, and no pass says it for one.
 *
 * <p>{@link ConstructionOrigin}'s arms are declared where only this package can name them, so a pass
 * elsewhere cannot make an origin. What it can still do is take one off a node and hand it to
 * another node's constructor, which is the same defect a step along: the answer would come from
 * wherever the writer happened to have one rather than from what the node is. So the two forms that
 * hold an origin are built through the constructors that take none, and the constructors that take
 * one are this package's to call.
 *
 * <p>Read off the compiled classes and not the source, because it is a rule about who calls what: a
 * reference is in the constant pool of the class that makes it whatever the call looks like. The
 * population is every class of every module, tests included — a rule about who may write an origin
 * that stopped at the module it was written in would be a rule about one build directory.
 *
 * <p>The name is matched whole and the argument types are read off the descriptor, so a component
 * added to either form leaves this saying what it said: what is looked for is a constructor of one
 * of the two forms that takes an origin, not the shape either form has today.
 */
class WhereAConstructionCameFromIsNotAPassesToWriteTest {

    private static final String ORIGIN = "Lsouther/compiler/ast/ConstructionOrigin;";

    private static final Set<String> HOLDS_ONE =
            Set.of("souther/compiler/ast/Hir$NewData", "souther/compiler/ast/Hir$Apply");

    /** Where the forms are written, and so where an origin may be handed to one. */
    private static final String THEIRS = "souther/compiler/ast/";

    @Test
    void nothingOutsideTheTreeWritesAnOriginIntoAConstruction() {
        List<String> writing = new ArrayList<>();
        for (Path each : everyCompiledClass()) {
            if (!handsAnOriginToAForm(each) || internalName(each).startsWith(THEIRS)) {
                continue;
            }
            writing.add(internalName(each));
        }

        assertEquals(List.of(), writing.stream().sorted().toList(),
                "a pass writing one of these forms says what it is building and not where the"
                        + " construction came from: the constructors that take no origin are the"
                        + " ones to call, and a rebuild carries the origin it was handed");
    }

    /** The control: the walk reads the classes it is about, and would see the reference it forbids
     *  where the two forms make it. */
    @Test
    void andTheCheckReadsEveryModuleAndSeesTheReferenceWhereItIsAllowed() {
        List<Path> classes = everyCompiledClass();

        assertTrue(classes.size() > 1000, "every module's classes: " + classes.size());
        assertTrue(classes.stream().anyMatch(each -> internalName(each).startsWith("souther/lsp/")
                        || internalName(each).startsWith("souther/fmt/")),
                "a module beside the compiler is in the population");
        assertTrue(classes.stream().filter(each -> internalName(each).endsWith("Hir$Apply"))
                        .anyMatch(WhereAConstructionCameFromIsNotAPassesToWriteTest
                                ::handsAnOriginToAForm),
                "the form itself hands an origin to its own constructor, which is what this reads");
    }

    /** Whether {@code compiled} names a constructor of a form that holds an origin, taking one. */
    private static boolean handsAnOriginToAForm(Path compiled) {
        try {
            for (PoolEntry entry : ClassFile.of().parse(Files.readAllBytes(compiled))
                    .constantPool()) {
                if (entry instanceof MemberRefEntry member
                        && member.name().stringValue().equals("<init>")
                        && HOLDS_ONE.contains(member.owner().name().stringValue())
                        && member.type().stringValue().contains(ORIGIN)) {
                    return true;
                }
            }
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
        return false;
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
        try (Stream<Path> modules = Files.list(Path.of("..").toAbsolutePath().normalize())) {
            for (Path module : modules.filter(Files::isDirectory).toList()) {
                for (String built : List.of("classes", "test-classes")) {
                    Path where = module.resolve("target").resolve(built);
                    if (!Files.isDirectory(where)) {
                        continue;
                    }
                    try (Stream<Path> found = Files.walk(where)) {
                        out.addAll(found.filter(p -> p.toString().endsWith(".class")).toList());
                    }
                }
            }
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
        return out;
    }
}
