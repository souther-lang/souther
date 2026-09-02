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
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * Who may settle what a construction was read as, and where.
 *
 * <p>Two checks beside this one read the caller: nothing outside {@code souther.compiler.ast} hands
 * an origin in, and nothing outside names which of its fields a construction had to write. Both see
 * an answer only where a call site spells one, so a member of the owning package that fills one in
 * for whoever calls it leaves every caller clean — which is what a constructor answering
 * {@code own} was, and what a factory answering {@code optionals may be omitted} would be.
 *
 * <p>What settles an answer is a member and the calls that reach it, so both are read here. The
 * members of the owning package that name an answer are listed, each by the whole of what it is, so
 * a second one of a name is a second row. And the calls that reach the members which <em>settle</em>
 * one are listed by who makes them, because a settling member is public and being unable to reach
 * its arguments is a thing about how the passes are written rather than one the language holds.
 *
 * <p>Neither list says what a rewrite is. The first is every member of a package, read off its
 * classes; the second is every call to one of them, read off the whole reactor. A pass added
 * tomorrow is in them or it does not settle an answer.
 */
class EveryPlaceAnAnswerAboutAConstructionIsNamedTest {

    private static final String THEIRS = "souther/compiler/ast/";

    private static final RepositoryLayout REPOSITORY = RepositoryLayout.ofWorkingDirectory();

    /**
     * The members that settle an answer rather than carrying or asking one: a source read, the
     * translation of an application into the construction it means, a pass composing one, and the
     * two crossings that make one answer out of another.
     *
     * <p>Named by owner and member, so every overload of one settles. Which overloads there are is
     * the other list's to hold.
     */
    private static final Set<String> SETTLES = Set.of(
            "souther/compiler/ast/Hir$NewData#read",
            "souther/compiler/ast/Hir$NewData#fromApply",
            "souther/compiler/ast/Hir$NewData#syntheticWithEveryFieldWritten",
            "souther/compiler/ast/Hir$NewData#publishedBy",
            "souther/compiler/ast/Hir$NewData#carriedByValue",
            "souther/compiler/ast/Hir$Apply#read",
            "souther/compiler/ast/Hir$Apply#synthetic",
            "souther/compiler/ast/Hir$Apply#carriedByValue");

    /**
     * Every member of the owning package that names an answer, by the whole of what it is — owner,
     * member, what it takes and what it answers with. A second member of a name is a second row, so
     * an overload that settles an answer of its own cannot stand behind one that already does.
     *
     * <p>Four settle one: {@code read} on each form is a source spelling it, {@code fromApply}
     * moves to a construction what the application it means already answered, and
     * {@code syntheticWithEveryFieldWritten} and {@code synthetic} are a pass writing one where no
     * source did. Three move an answer along the crossings a construction has:
     * {@code publishedBy}, {@code carriedByValue} and the {@code Origins} members that say what
     * each crossing does. The rest carry or ask — {@code with}, {@code withArgs},
     * {@code withFunction} and {@code standingIn} put back what they were handed and
     * {@code atSlots} and {@code withRegion} are the rewrites that go through them, while
     * {@code mayOmitOptionalFields}, {@code wasCarried}, {@code wasCarriedByValue} and
     * {@code Origins#carried} are the questions a check puts to a node. The accessors and the
     * enum's own members are here because naming an answer is what an accessor does.
     *
     * <p>An overload that only hands its arguments to one of these is not here, and needs not be:
     * it settles nothing itself, and a call to it is a call to what it delegates to, which the
     * other list holds.
     */
    private static final List<String> NAMING = List.of(
            "souther/compiler/ast/Hir#atSlots(Lsouther/compiler/ast/Hir$Expr;Ljava/util/function/UnaryOperator;Ljava/util/function/UnaryOperator;)Lsouther/compiler/ast/Hir$Expr;",
            "souther/compiler/ast/Hir#withRegion(Lsouther/compiler/ast/Hir$Expr;Lsouther/compiler/diag/Region;)Lsouther/compiler/ast/Hir$Expr;",
            "souther/compiler/ast/Hir$Apply#carriedByValue()Lsouther/compiler/ast/Hir$Apply;",
            "souther/compiler/ast/Hir$Apply#origin()Lsouther/compiler/ast/ConstructionOrigin;",
            "souther/compiler/ast/Hir$Apply#read(Lsouther/compiler/ast/Ast$Apply;Lsouther/compiler/ast/Hir$Expr;Ljava/util/List;)Lsouther/compiler/ast/Hir$Apply;",
            "souther/compiler/ast/Hir$Apply#standingIn(Ljava/lang/String;)Lsouther/compiler/ast/Hir$Apply;",
            "souther/compiler/ast/Hir$Apply#synthetic(Lsouther/compiler/ast/Hir$Expr;Ljava/util/List;Lsouther/compiler/diag/SourcePos;Lsouther/compiler/diag/Region;)Lsouther/compiler/ast/Hir$Apply;",
            "souther/compiler/ast/Hir$Apply#wasCarriedByValue()Z",
            "souther/compiler/ast/Hir$Apply#with(Lsouther/compiler/ast/Hir$Expr;Ljava/util/List;Lsouther/compiler/diag/SourcePos;Lsouther/compiler/diag/Region;)Lsouther/compiler/ast/Hir$Apply;",
            "souther/compiler/ast/Hir$Apply#withArgs(Ljava/util/List;)Lsouther/compiler/ast/Hir$Apply;",
            "souther/compiler/ast/Hir$Apply#withFunction(Lsouther/compiler/ast/Hir$Expr;)Lsouther/compiler/ast/Hir$Apply;",
            "souther/compiler/ast/Hir$Fields#$values()[Lsouther/compiler/ast/Hir$Fields;",
            "souther/compiler/ast/Hir$Fields#values()[Lsouther/compiler/ast/Hir$Fields;",
            "souther/compiler/ast/Hir$NewData#carriedByValue()Lsouther/compiler/ast/Hir$NewData;",
            "souther/compiler/ast/Hir$NewData#fields()Lsouther/compiler/ast/Hir$Fields;",
            "souther/compiler/ast/Hir$NewData#fromApply(Lsouther/compiler/ast/Hir$Apply;Lsouther/compiler/ast/Hir$Name;Ljava/util/List;)Lsouther/compiler/ast/Hir$NewData;",
            "souther/compiler/ast/Hir$NewData#mayOmitOptionalFields()Z",
            "souther/compiler/ast/Hir$NewData#origin()Lsouther/compiler/ast/ConstructionOrigin;",
            "souther/compiler/ast/Hir$NewData#publishedBy(Ljava/lang/String;)Lsouther/compiler/ast/Hir$NewData;",
            "souther/compiler/ast/Hir$NewData#read(Lsouther/compiler/ast/Ast$NewData;Lsouther/compiler/ast/Hir$Name;Ljava/util/List;Ljava/util/List;Lsouther/compiler/ast/Reading;)Lsouther/compiler/ast/Hir$NewData;",
            "souther/compiler/ast/Hir$NewData#syntheticWithEveryFieldWritten(Lsouther/compiler/ast/Hir$Name;Ljava/util/List;Ljava/util/List;Lsouther/compiler/diag/SourcePos;Lsouther/compiler/diag/Region;)Lsouther/compiler/ast/Hir$NewData;",
            "souther/compiler/ast/Hir$NewData#wasCarried(Lsouther/compiler/types/TypeSymbol$AtModule;)Z",
            "souther/compiler/ast/Hir$NewData#with(Ljava/util/List;Ljava/util/List;Lsouther/compiler/diag/SourcePos;Lsouther/compiler/diag/Region;)Lsouther/compiler/ast/Hir$NewData;",
            "souther/compiler/ast/Origins#carried(Lsouther/compiler/ast/ConstructionOrigin;Lsouther/compiler/types/TypeSymbol$AtModule;)Z",
            "souther/compiler/ast/Origins#carriedByValue(Lsouther/compiler/ast/ConstructionOrigin;)Lsouther/compiler/ast/ConstructionOrigin;",
            "souther/compiler/ast/Origins#publishedIn(Lsouther/compiler/ast/ConstructionOrigin;Ljava/lang/String;)Lsouther/compiler/ast/ConstructionOrigin;",
            "souther/compiler/ast/Origins$Published#module()Ljava/lang/String;");

    /**
     * Every call that settles an answer, and who makes it.
     *
     * <p>A source is read in one place: {@code Resolve} is what reads one, and it is the only caller
     * of either {@code read}. The crossings are {@code HelperNames}', which is what carries a body
     * into a reader. {@code NewtypeDesugar} is where an application means a construction. The rest
     * compose an application or a fixture no source spells, and each says so where it calls.
     *
     * <p>A row whose caller is not one of those is a pass answering for something it did not read.
     * Being able to call one of these is not what stops it — the forms are public and a parsed node
     * is a record anyone can build — so what stops it is this list.
     */
    private static final List<String> SETTLING = List.of(
            "souther/compiler/ast/Hir$Apply -> souther/compiler/ast/Hir$Apply#synthetic",
            "souther/compiler/check/Elaborator -> souther/compiler/ast/Hir$Apply#synthetic",
            "souther/compiler/check/HelperInliner -> souther/compiler/ast/Hir$Apply#synthetic",
            "souther/compiler/check/HelperNames -> souther/compiler/ast/Hir$Apply#carriedByValue",
            "souther/compiler/check/HelperNames -> souther/compiler/ast/Hir$NewData#carriedByValue",
            "souther/compiler/check/HelperNames -> souther/compiler/ast/Hir$NewData#publishedBy",
            "souther/compiler/check/NewtypeDesugar -> souther/compiler/ast/Hir$NewData#fromApply",
            "souther/compiler/check/Resolve -> souther/compiler/ast/Hir$Apply#read",
            "souther/compiler/check/Resolve -> souther/compiler/ast/Hir$NewData#read",
            "souther/compiler/check/Terms -> souther/compiler/ast/Hir$Apply#synthetic",
            "souther/compiler/partition/FixtureTemplate -> souther/compiler/ast/Hir$Apply#synthetic",
            "souther/compiler/partition/FixtureTemplate -> souther/compiler/ast/Hir$NewData#syntheticWithEveryFieldWritten");

    @Test
    void everyMemberOfTheOwningPackageThatNamesAnAnswerIsWrittenDown() {
        assertEquals(NAMING, new ArrayList<>(namingAnAnswer()),
                "a row here is a way to answer what a construction was read as, or a reader of one:"
                        + " say which it is and why it is not the node's own answer carried");
    }

    @Test
    void andEveryCallThatSettlesOneIsWrittenDownWithWhoMakesIt() {
        assertEquals(SETTLING, new ArrayList<>(settlingAnAnswer()),
                "settling an answer is the reading's to do and the crossings': a pass that rewrites"
                        + " a body carries what it was handed, and a row here that is not a reading"
                        + " or a crossing is a pass answering for a construction it did not read");
    }

    /** The control: the walk reads the whole reactor and not only the package it is about, which is
     *  where the calls it lists are made. */
    @Test
    void andTheWalkReadsEveryModulesClasses() {
        assertFalse(everyCompiledClass().stream()
                        .allMatch(each -> internalName(each).startsWith(THEIRS)),
                "the calls this reads are made outside the package that declares what they reach");
    }

    /** Every method of the owning package whose code names an answer, by owner, name and what it
     *  takes and answers with — so a second member of a name is a second row. */
    private static Set<String> namingAnAnswer() {
        Set<String> found = new TreeSet<>();
        for (Path each : everyCompiledClass()) {
            if (!internalName(each).startsWith(THEIRS)) {
                continue;
            }
            ClassModel model = parse(each);
            for (MethodModel method : model.methods()) {
                if (namesAnAnswer(method)) {
                    found.add(model.thisClass().name().stringValue() + "#"
                            + method.methodName().stringValue()
                            + method.methodType().stringValue());
                }
            }
        }
        return found;
    }

    /** Every call to a settling member, as the class that makes it and what it settles. */
    private static Set<String> settlingAnAnswer() {
        Set<String> found = new TreeSet<>();
        for (Path each : everyCompiledClass()) {
            ClassModel model = parse(each);
            for (MethodModel method : model.methods()) {
                method.code().ifPresent(code -> {
                    for (CodeElement element : code) {
                        if (element instanceof InvokeInstruction invoked
                                && SETTLES.contains(invoked.owner().name().stringValue() + "#"
                                        + invoked.name().stringValue())) {
                            found.add(internalName(each) + " -> "
                                    + invoked.owner().name().stringValue() + "#"
                                    + invoked.name().stringValue());
                        }
                    }
                });
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

    private static ClassModel parse(Path compiled) {
        try {
            return ClassFile.of().parse(Files.readAllBytes(compiled));
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    /** The class's own binary name, read off the file's place under its module's build directory. */
    private static String internalName(Path compiled) {
        String path = compiled.toString().replace('\\', '/');
        int from = path.indexOf("/classes/") + "/classes/".length();
        return path.substring(from, path.length() - ".class".length());
    }

    /**
     * The compiled classes of every module of this build that the compiler is made of.
     *
     * <p>Its own tests are not among them. A test builds a node to look at it and ships nothing, so
     * what it names is not an answer anything downstream reads; and a list holding them would move
     * whenever a test was written, which is a list nobody keeps up.
     */
    private static List<Path> everyCompiledClass() {
        List<Path> out = new ArrayList<>();
        for (Path module : REPOSITORY.modules()) {
            Path where = module.resolve("target").resolve("classes");
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
