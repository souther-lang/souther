package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Prepared;

import java.io.IOException;
import java.lang.classfile.Attributes;
import java.lang.classfile.ClassFile;
import java.lang.classfile.ClassModel;
import java.lang.classfile.FieldModel;
import java.lang.classfile.MethodModel;
import java.lang.classfile.MethodSignature;
import java.lang.classfile.Signature;
import java.lang.classfile.attribute.RecordAttribute;
import java.lang.classfile.attribute.RecordComponentInfo;
import java.lang.constant.ClassDesc;
import java.lang.constant.ConstantDescs;
import java.net.URISyntaxException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Only a row is called a row.
 *
 * <p>A row is one line of an {@code example} or {@code fake} table. The things holding rows nest —
 * a block holds rows, a module's preparation holds blocks, a report holds a number of them — and
 * every one of those levels can be spelled {@code rows} without a reader being told which they have.
 * A count taken off the wrong level is a count of blocks that reads as a count of rows, and the
 * name is what produced the expectation.
 *
 * <p><b>Two prohibitions, because a level can be named twice.</b> A declaration names a level by
 * what it calls the member that answers it, and by what it calls the type that is it. Closing only
 * the member leaves a type free to be called {@code Rows} while holding blocks, which is where this
 * was found.
 *
 * <p><b>What is reserved is the bare name.</b> {@code row} and {@code rows} exactly, and the types
 * {@code Row} and {@code Rows} exactly. A compound name has a different head concept —
 * {@code rowCount} is a number, {@code RowReading} is a reading, {@code RowsRead} is what was read
 * — and a rule that took names apart into tokens would be a naming lint rather than this claim.
 * Nothing here says a compound name holds rows; only that the bare name is not available to
 * anything else.
 *
 * <p><b>What it is over is production declarations.</b> It reads the main class files of this
 * module, which is where the row vocabulary is declared and where a reader of this compiler meets
 * it. Test fixtures, local variables and parameters are not part of the surface it protects: a
 * table-driven test's own {@code Row} is not a name any reader of the compiler resolves, and what a
 * method calls a value inside its body is not a declaration. Serialized vocabulary is outside it
 * too — a report's JSON key {@code "rows"} is a wire contract of its own and is not renamed by
 * anything said here.
 */
class OnlyARowIsCalledARowTest {

    /**
     * The rows of this compiler.
     *
     * <p>The declaration of what the word means. A value of one of these types is one row itself,
     * at whichever stage the type belongs to — what an author wrote, what the check settled, what a
     * run recorded, what a generator offered. A line stays a line all the way along, so the list is
     * a chain and not a layer.
     *
     * <p>What is not on it is everything that is <em>about</em> a row. An identity, a reference, an
     * id, a key, a reading, a verdict, a deadline and a unit of work each hold a row's whereabouts
     * beside something else, and a reader handed one of them under the bare name would take it for
     * the line.
     */
    private static final Set<String> ROWS = Set.of(
            "souther/compiler/ast/Ast$ExampleRow",
            "souther/compiler/ast/Ast$FakeRow",
            "souther/compiler/ast/Hir$ExampleRow",
            "souther/compiler/ast/Hir$FakeRow",
            "souther/compiler/examples/RecordedRow",
            "souther/compiler/observe/RowOutcome",
            "souther/compiler/partition/Generator$GeneratedRow",
            "souther/compiler/program/CheckedRow",
            "souther/compiler/query/OfferedRow",
            "souther/compiler/query/Output$RowsRead$ReadRow");

    /**
     * What a plurality of rows is held in.
     *
     * <p>A closed list, so that a shape nobody has decided about arrives here as a failure rather
     * than as a pass. A map from something to rows is not on it: what its keys are is a second
     * thing the value says, and a name that does not say it leaves the reader to find out.
     */
    private static final Set<String> CONTAINERS = Set.of(
            "java/util/Collection",
            "java/util/List",
            "java/util/SequencedCollection",
            "java/util/Set");

    private static final Set<String> RESERVED_MEMBERS = Set.of("row", "rows");

    private static final Set<String> RESERVED_TYPES = Set.of("Row", "Rows");

    /** A member called {@code row} or {@code rows} answers a row, or rows. */
    @Test
    void aMemberCalledRowAnswersARow() throws IOException, URISyntaxException {
        List<String> wrong = new ArrayList<>();
        for (ClassModel each : compiled()) {
            wrong.addAll(membersOf(each));
        }
        assertEquals(List.of(), wrong,
                "a member called row or rows answers a row or rows, and these answer something else");
    }

    /** A type called {@code Row} or {@code Rows} is a row, or is rows. */
    @Test
    void aTypeCalledRowIsARow() throws IOException, URISyntaxException {
        List<String> wrong = new ArrayList<>();
        for (ClassModel each : compiled()) {
            String internal = internal(each);
            if (RESERVED_TYPES.contains(simple(internal)) && !ROWS.contains(internal)) {
                wrong.add(internal);
            }
        }
        assertEquals(List.of(), wrong,
                "a type called Row or Rows is a row, and these are something else");
    }

    /**
     * And both prohibitions are over something.
     *
     * <p>Both pass on the empty set, which is also what a walk that read nothing answers. The rows
     * are the population the member rule is about — a name it lets through rather than one it never
     * met — and the classes are what the type rule ranges over. Told neither, a walk that had lost
     * its way would report this module clean.
     */
    @Test
    void bothOfThoseAreOverSomething() throws IOException, URISyntaxException {
        List<ClassModel> compiled = compiled();
        assertTrue(compiled.size() > 100,
                "the walk reads this module's classes, and read " + compiled.size());
        List<String> allowed = new ArrayList<>();
        for (ClassModel each : compiled) {
            for (MethodModel method : each.methods()) {
                if (RESERVED_MEMBERS.contains(method.methodName().stringValue())
                        && answersARow(answeredBy(method))) {
                    allowed.add(internal(each) + "." + method.methodName().stringValue());
                }
            }
        }
        assertFalse(allowed.isEmpty(), "the reserved name is in use on what may hold it");
    }

    /**
     * Every declaration of one class that takes the reserved name.
     *
     * <p>One name of one class is one finding. A record component, the field it writes and the
     * accessor that answers it are one thing the author wrote, and so are a field and the accessor
     * beside it; naming each of them would say the same finding three times over.
     */
    private static List<String> membersOf(ClassModel of) {
        List<String> wrong = new ArrayList<>();
        Set<String> said = new LinkedHashSet<>();
        Set<String> components = new LinkedHashSet<>();
        for (RecordComponentInfo each : of.findAttribute(Attributes.record())
                .map(RecordAttribute::components).orElse(List.of())) {
            components.add(each.name().stringValue());
            if (RESERVED_MEMBERS.contains(each.name().stringValue())
                    && !answersARow(signatureOf(each)) && said.add(each.name().stringValue())) {
                wrong.add(internal(of) + "." + each.name().stringValue()
                        + " : " + shown(signatureOf(each)));
            }
        }
        for (FieldModel each : of.fields()) {
            String name = each.fieldName().stringValue();
            if (RESERVED_MEMBERS.contains(name) && !components.contains(name)
                    && !answersARow(signatureOf(each)) && said.add(name)) {
                wrong.add(internal(of) + "." + name + " : " + shown(signatureOf(each)));
            }
        }
        for (MethodModel each : of.methods()) {
            String name = each.methodName().stringValue();
            if (RESERVED_MEMBERS.contains(name) && !components.contains(name)
                    && !answersARow(answeredBy(each)) && said.add(name)) {
                wrong.add(internal(of) + "." + name + " : " + shown(answeredBy(each)));
            }
        }
        return wrong;
    }

    /**
     * Whether what a member answers is a row, or rows.
     *
     * <p>An array of rows is rows for the same reason a list of them is. A number is not: what it
     * counts is not in it, which is how a count of blocks comes to be read as a count of rows.
     */
    private static boolean answersARow(Signature answered) {
        return switch (answered) {
            case Signature.ArrayTypeSig array -> answersARow(array.componentSignature());
            case Signature.ClassTypeSig cls -> ROWS.contains(named(cls))
                    || CONTAINERS.contains(named(cls)) && cls.typeArgs().size() == 1
                    && answersARow(argument(cls.typeArgs().getFirst()));
            default -> false;
        };
    }

    /** What a type argument stands for, or the type variable that stands for nothing here. */
    private static Signature argument(Signature.TypeArg arg) {
        return switch (arg) {
            case Signature.TypeArg.Bounded bounded -> bounded.boundType();
            case Signature.TypeArg.Unbounded _ -> Signature.of(ConstantDescs.CD_Object);
        };
    }

    private static String named(Signature.ClassTypeSig of) {
        String descriptor = of.classDesc().descriptorString();
        return descriptor.substring(1, descriptor.length() - 1);
    }

    /** What a method answers, generic where it was written generic. */
    private static Signature answeredBy(MethodModel of) {
        Optional<MethodSignature> generic = of.findAttribute(Attributes.signature())
                .map(it -> MethodSignature.parseFrom(it.signature().stringValue()));
        return generic.map(MethodSignature::result)
                .orElseGet(() -> Signature.of(of.methodTypeSymbol().returnType()));
    }

    private static Signature signatureOf(FieldModel of) {
        return of.findAttribute(Attributes.signature())
                .map(it -> Signature.parseFrom(it.signature().stringValue()))
                .orElseGet(() -> Signature.of(of.fieldTypeSymbol()));
    }

    private static Signature signatureOf(RecordComponentInfo of) {
        return of.findAttribute(Attributes.signature())
                .map(it -> Signature.parseFrom(it.signature().stringValue()))
                .orElseGet(() -> Signature.of(of.descriptorSymbol()));
    }

    private static String shown(Signature of) {
        return switch (of) {
            case Signature.ArrayTypeSig array -> shown(array.componentSignature()) + "[]";
            case Signature.BaseTypeSig base ->
                    ClassDesc.ofDescriptor(String.valueOf(base.baseType())).displayName();
            case Signature.TypeVarSig var -> var.identifier();
            case Signature.ClassTypeSig cls -> cls.typeArgs().isEmpty() ? named(cls)
                    : named(cls) + "<" + String.join(", ",
                            cls.typeArgs().stream().map(it -> shown(argument(it))).toList()) + ">";
        };
    }

    private static String internal(ClassModel of) {
        return of.thisClass().asInternalName();
    }

    private static String simple(String internal) {
        String last = internal.substring(internal.lastIndexOf('/') + 1);
        return last.substring(last.lastIndexOf('$') + 1);
    }

    /** Every class this compiler was built into, found from where one of them is loaded from. */
    private static List<ClassModel> compiled() throws IOException, URISyntaxException {
        Path root = Path.of(Prepared.class.getResource("Prepared.class").toURI());
        for (int up = 0; up <= "souther/compiler/check".chars().filter(it -> it == '/').count();
                up++) {
            root = root.getParent();
        }
        List<ClassModel> out = new ArrayList<>();
        try (Stream<Path> walk = Files.walk(root)) {
            for (Path each : walk.filter(it -> it.toString().endsWith(".class")).sorted().toList()) {
                out.add(ClassFile.of().parse(Files.readAllBytes(each)));
            }
        }
        return out;
    }
}
