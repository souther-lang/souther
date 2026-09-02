package souther.architecture;

import souther.compiler.ast.ConstructionOrigin;
import souther.compiler.ast.Hir;
import souther.test.RepositoryLayout;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.lang.classfile.ClassFile;
import java.lang.classfile.ClassModel;
import java.lang.classfile.CodeElement;
import java.lang.classfile.MethodModel;
import java.lang.classfile.instruction.FieldInstruction;
import java.lang.classfile.instruction.InvokeInstruction;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Every place an answer about a construction is named, named.
 *
 * <p>Two checks beside this one forbid a pass outside {@code souther.compiler.ast} from handing an
 * origin in or from naming which of its fields a construction had to write. Both read the caller,
 * and so both see only an answer spelled at a call site: a member of this package that fills one in
 * for whoever calls it leaves the caller's classes clean, and that is what a constructor answering
 * {@code own} was, and what a factory answering {@code optionals may be omitted} would be. A check
 * over callers cannot see a decision made one level down.
 *
 * <p>So this reads where the decisions are. Every method of the owning package whose code names an
 * answer — a constant of one, a member taking or answering with one — is listed, and the list is
 * written down. Adding a way to answer adds a row and this goes red, which is what makes a new one
 * something to say out loud rather than something to slip in behind a name.
 *
 * <p>Reads are in the list beside the answers themselves, because telling one from the other means
 * reading intent out of bytecode. The list is the surface the answers have, and what each row is for
 * is said where it is written.
 */
class EveryPlaceAnAnswerAboutAConstructionIsNamedTest {

    private static final String THEIRS = "souther/compiler/ast/";

    private static final RepositoryLayout REPOSITORY = RepositoryLayout.ofWorkingDirectory();

    /**
     * Every place the owning package names an answer, and what each is for.
     *
     * <p>Four of them settle one. {@code read} is a source that spells a construction or an
     * application; {@code fromApply} moves to a construction the answer the application it means
     * already gave; {@code synthetic} and {@code syntheticWithEveryFieldWritten} are a pass writing
     * one where no source did, each named for what it answers. A fifth kind moves an answer along
     * the crossings it has: {@code publishedBy}, {@code carriedByValue}, and the {@code Origins}
     * members that say what each crossing does to one.
     *
     * <p>The rest carry or ask. {@code with}, {@code withArgs}, {@code withFunction} and
     * {@code standingIn} put back what they were handed; {@code atSlots} and {@code withRegion} are
     * the rewrites that go through them. {@code mayOmitOptionalFields}, {@code wasCarried},
     * {@code wasCarriedByValue} and {@code Origins#carried} are the questions a check puts to a
     * node. The accessors and the enum's own members are here because naming an answer is what an
     * accessor does.
     */
    private static final List<String> SURFACE = List.of(
            "Apply#carriedByValue",
            "Apply#origin",
            "Apply#read",
            "Apply#standingIn",
            "Apply#synthetic",
            "Apply#wasCarriedByValue",
            "Apply#with",
            "Apply#withArgs",
            "Apply#withFunction",
            "Fields#$values",
            "Fields#values",
            "Hir#atSlots",
            "Hir#withRegion",
            "NewData#carriedByValue",
            "NewData#fields",
            "NewData#fromApply",
            "NewData#mayOmitOptionalFields",
            "NewData#origin",
            "NewData#publishedBy",
            "NewData#read",
            "NewData#syntheticWithEveryFieldWritten",
            "NewData#wasCarried",
            "NewData#with",
            "Origins#carried",
            "Origins#carriedByValue",
            "Origins#publishedIn",
            "Published#module");

    @Test
    void everyPlaceTheOwningPackageAnswersOrAsksIsWrittenDown() {
        assertEquals(SURFACE, new ArrayList<>(namingAnAnswer()),
                "a row added here is a new way to answer what a construction was read as, or a new"
                        + " reader of one: say which it is and why it is not the node's own answer"
                        + " carried");
    }

    /** Every method of the owning package whose code names an answer, as {@code Form#method}. */
    private static Set<String> namingAnAnswer() {
        Set<String> found = new TreeSet<>();
        for (Path each : everyCompiledClassOfTheTree()) {
            ClassModel model = parse(each);
            String form = simpleName(model.thisClass().name().stringValue());
            for (MethodModel method : model.methods()) {
                if (namesAnAnswer(method)) {
                    found.add(form + "#" + method.methodName().stringValue());
                }
            }
        }
        return found;
    }

    /** Whether {@code method}'s code names an answer: a constant of one, or a member that takes one
     *  or answers with one. A class initialiser is what makes the constants and is not one. */
    private static boolean namesAnAnswer(MethodModel method) {
        if (method.methodName().stringValue().startsWith("<")) {
            return false;
        }
        return method.code().map(code -> {
            for (CodeElement element : code) {
                if (element instanceof FieldInstruction field
                        && (isAnAnswer(field.owner().name().stringValue())
                                || mentionsAnAnswer(field.typeSymbol().descriptorString()))) {
                    return true;
                }
                if (element instanceof InvokeInstruction invoked
                        && (isAnAnswer(invoked.owner().name().stringValue())
                                || mentionsAnAnswer(invoked.typeSymbol().descriptorString()))) {
                    return true;
                }
            }
            return false;
        }).orElse(false);
    }

    private static boolean isAnAnswer(String internalName) {
        return anAnswer().contains("L" + internalName + ";");
    }

    private static boolean mentionsAnAnswer(String descriptor) {
        return anAnswer().stream().anyMatch(descriptor::contains);
    }

    /** What an answer is, read off the types: which of its fields a construction had to write, and
     *  where it came from with each of the arms that says so. */
    private static Set<String> anAnswer() {
        Set<String> descriptors = new LinkedHashSet<>();
        descriptors.add(descriptorOf(Hir.Fields.class));
        descriptors.add(descriptorOf(ConstructionOrigin.class));
        for (Class<?> arm : ConstructionOrigin.class.getPermittedSubclasses()) {
            descriptors.add(descriptorOf(arm));
        }
        return descriptors;
    }

    private static String descriptorOf(Class<?> type) {
        return "L" + type.getName().replace('.', '/') + ";";
    }

    private static String simpleName(String internalName) {
        return internalName.substring(Math.max(internalName.lastIndexOf('/'),
                internalName.lastIndexOf('$')) + 1);
    }

    private static ClassModel parse(Path compiled) {
        try {
            return ClassFile.of().parse(Files.readAllBytes(compiled));
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    /** The compiled classes of the package that owns the answers. */
    private static List<Path> everyCompiledClassOfTheTree() {
        List<Path> out = new ArrayList<>();
        for (Path module : REPOSITORY.modules()) {
            Path where = module.resolve("target").resolve("classes").resolve(THEIRS);
            if (!Files.isDirectory(where)) {
                continue;
            }
            try (Stream<Path> found = Files.walk(where)) {
                out.addAll(found.filter(p -> p.toString().endsWith(".class")).toList());
            } catch (IOException e) {
                throw new UncheckedIOException(e);
            }
        }
        return out;
    }
}
