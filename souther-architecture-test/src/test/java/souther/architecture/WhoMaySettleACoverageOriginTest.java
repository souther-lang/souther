package souther.architecture;

import souther.compiler.types.CoverageConstruct;
import souther.compiler.types.CoverageOrigin;
import souther.test.RepositoryLayout;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.lang.classfile.ClassFile;
import java.lang.classfile.ClassModel;
import java.lang.classfile.CodeElement;
import java.lang.classfile.MethodModel;
import java.lang.classfile.instruction.InvokeInstruction;
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
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * Who may say which construct a coverage obligation was written as.
 *
 * <p>A non-recursive helper is expanded at each call, so one construct the author wrote becomes
 * several in the tree that runs, and what says those copies are one obligation is that they carry
 * one origin. An origin minted after that expansion gives two copies of one construct two, which is
 * the thing the type exists to prevent. Its own account says where one may be made: at the reading
 * of a source construct, at a rewrite that reads a call back as the comparison it means and has no
 * source to answer for, and at the derivation of the forks a lowering makes.
 *
 * <p>Nothing held that. The record's canonical constructor is public, as a record's is, and takes
 * every component; a member that answers for its caller leaves the caller's classes clean. So the
 * account is read off the compiled classes here instead: every call that settles an origin, with who
 * makes it. A row added is a place answering for a construct it did not read.
 *
 * <p>Not the shape its neighbours have. Where a construction came from and which of its fields had
 * to be written are answered by asking the node, so their vocabulary stays inside the package that
 * owns it and a check over callers is enough. What reads an origin reads the module, the construct
 * and the fork, so the vocabulary crosses and the calls are what there is to read.
 */
class WhoMaySettleACoverageOriginTest {

    /** Read off the type, so that renaming it stops the build rather than leaving this walk with
     *  nothing to find and nothing to say. */
    private static final String OWNER = internalNameOf(CoverageOrigin.class);

    private static final String AN_ORIGIN = "L" + OWNER + ";";

    private static final String A_CONSTRUCT = "L" + internalNameOf(CoverageConstruct.class) + ";";

    private static String internalNameOf(Class<?> type) {
        return type.getName().replace('.', '/');
    }

    private static final RepositoryLayout REPOSITORY = RepositoryLayout.ofWorkingDirectory();

    /**
     * The members that settle an origin: whatever answers with one, and the constructor they all go
     * through.
     *
     * <p>Read off the type rather than written out, so a member added beside them is one of these by
     * being one. A list spelled here would be a list of what was thought of, and a way to make an
     * origin that this walk then passed over is the way one would come to be made.
     *
     * <p>Each is named by what it takes and answers with, and not by its name alone. A fork is
     * derived by {@code lowered} taking the part it is of, and the fork a value already is, is read
     * by {@code lowered} taking nothing — one name over a derivation and an accessor, which a key
     * made of names alone puts in one row and reports a reader as a writer.
     */
    private static Set<String> settlingMembers() {
        Set<String> members = new TreeSet<>();
        for (Method each : CoverageOrigin.class.getDeclaredMethods()) {
            if (each.getReturnType() == CoverageOrigin.class) {
                members.add(OWNER + "#" + each.getName() + descriptorOf(
                        each.getParameterTypes(), each.getReturnType()));
            }
        }
        for (Constructor<?> each : CoverageOrigin.class.getDeclaredConstructors()) {
            members.add(OWNER + "#<init>" + descriptorOf(each.getParameterTypes(), void.class));
        }
        return members;
    }

    /**
     * What settling an origin looks like, written down — so that a way of doing it that is added is
     * a row here before anyone calls it, and not a silence.
     */
    private static final List<String> SETTLES = List.of(
            OWNER + "#<init>(Ljava/lang/String;II" + A_CONSTRUCT + ")V",
            OWNER + "#lowered(I)" + AN_ORIGIN,
            OWNER + "#unwritten()" + AN_ORIGIN,
            OWNER + "#written(Ljava/lang/String;I" + A_CONSTRUCT + ")" + AN_ORIGIN);

    @Test
    void everyWayOfSettlingOneIsWrittenDown() {
        assertEquals(SETTLES, new ArrayList<>(settlingMembers()),
                "a row added here is a way to say which construct an obligation was written as:"
                        + " say what reads a source to answer it, and add the calls that reach it");
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

    /**
     * Every call that settles an origin, and who makes it.
     *
     * <p>A source construct is read in one place. {@code TheOtherCase}, {@code Terms} and
     * {@code Conditions} read a preserved call back as the comparison it means, and a preserved call
     * holds no origin, so there is none to carry and each says which it is answering. The fork of a
     * comprehension's guard is derived where the comprehension is, so that the lowering and the
     * reading that runs before it cannot number the guards differently.
     *
     * <p>The constructor is reached only from the members above. A row naming it elsewhere is a
     * pass minting an origin of its own, which after an expansion is two obligations where the
     * author wrote one.
     */
    private static final List<String> SETTLING = List.of(
            "souther/compiler/ast/Hir$ListComp -> souther/compiler/types/CoverageOrigin#lowered",
            "souther/compiler/check/Conditions -> souther/compiler/types/CoverageOrigin#unwritten",
            "souther/compiler/check/Conditions$AsPolar -> souther/compiler/types/CoverageOrigin#unwritten",
            "souther/compiler/check/Terms -> souther/compiler/types/CoverageOrigin#unwritten",
            "souther/compiler/check/TheOtherCase -> souther/compiler/types/CoverageOrigin#unwritten",
            "souther/compiler/frontend/AstBuilder -> souther/compiler/types/CoverageOrigin#written",
            "souther/compiler/types/CoverageOrigin -> souther/compiler/types/CoverageOrigin#<init>");

    @Test
    void everyCallThatSettlesOneIsWrittenDownWithWhoMakesIt() {
        assertEquals(SETTLING, new ArrayList<>(settlingAnOrigin()),
                "an origin is made where a source is read and where a rewrite has no source to"
                        + " answer for, and derived where a lowering forks one construct into"
                        + " several: a row that is neither is a copy given an obligation of its own");
    }

    /** The control: the walk reads the whole reactor and not only the class it is about, which is
     *  where the calls it lists are made. */
    @Test
    void andTheWalkReadsEveryModulesClasses() {
        assertFalse(everyCompiledClass().stream()
                        .allMatch(each -> internalName(each).startsWith(OWNER)),
                "the calls this reads are made outside the class that declares what they reach");
    }

    /** Every call to a settling member, as the class that makes it and what it settles. */
    private static Set<String> settlingAnOrigin() {
        Set<String> found = new TreeSet<>();
        for (Path each : everyCompiledClass()) {
            ClassModel model = parse(each);
            for (MethodModel method : model.methods()) {
                method.code().ifPresent(code -> {
                    for (CodeElement element : code) {
                        if (element instanceof InvokeInstruction invoked
                                && settlingMembers().contains(
                                        invoked.owner().name().stringValue() + "#"
                                        + invoked.name().stringValue()
                                        + invoked.typeSymbol().descriptorString())) {
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
     * <p>Its own tests are not among them. A test builds an origin to look at it and ships nothing,
     * and a list that moved whenever one was written is a list nobody keeps up.
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
