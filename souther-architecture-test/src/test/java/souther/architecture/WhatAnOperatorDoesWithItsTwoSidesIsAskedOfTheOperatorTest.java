package souther.architecture;

import org.junit.jupiter.api.Test;
import souther.compiler.types.BinOp;

import java.lang.classfile.ClassModel;
import java.lang.classfile.CodeElement;
import java.lang.classfile.CodeModel;
import java.lang.classfile.Instruction;
import java.lang.classfile.MethodModel;
import java.lang.classfile.Opcode;
import java.lang.classfile.instruction.FieldInstruction;
import java.lang.classfile.instruction.InvokeDynamicInstruction;
import java.lang.classfile.instruction.InvokeInstruction;
import java.lang.constant.ClassDesc;
import java.lang.constant.ConstantDesc;
import java.lang.constant.DynamicConstantDesc;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What {@code &&} and {@code ||} do with their two sides is asked of the operator, and never read
 * off which of the two it is.
 *
 * <p>Two questions, each with one owner. When the right side runs is
 * {@link BinOp#rightRunsWhenLeftIs} (and {@link BinOp#stopsWhenItsAnswerIsSettled}); what the two
 * conditions come to together is {@code ConditionJoin}, and which operators join two at all
 * {@link BinOp#joinsTwoConditions}. A reader that tells {@code AND} or {@code OR} apart for itself
 * writes one of those answers again, and one that writes when the right runs for itself can leave
 * it out, reading the right of {@code &&} as run on every run and sites no run reaches as reached.
 *
 * <p>So the two are named in few ways. Outside the owners, and the one place the operator the
 * source wrote becomes the language's, nothing reads either of them except to build the table of a
 * {@code switch}; and a {@code switch} naming either names every operator, so that the language
 * adding one stops the build there and has it decided about. That closes a comparison however it
 * is written — at once, through a local, in a collection — and a {@code switch} with a default arm
 * that answers for the operators it does not name. What it does not close is a reader reaching the
 * constants by reflection, by name or by position, which nothing here does.
 */
class WhatAnOperatorDoesWithItsTwoSidesIsAskedOfTheOperatorTest {

    private static final String OPERATOR = "souther/compiler/types/BinOp";
    private static final String SWITCHES = "java/lang/runtime/SwitchBootstraps";
    private static final Set<String> CONNECTIVES = Set.of("AND", "OR");
    private static final Set<String> EVERY_OPERATOR = everyOperator();

    /** The owners themselves, the one place each answer is written. */
    private static final Set<String> OWNERS = Set.of(OPERATOR,
            "souther/compiler/semantics/ConditionJoin");

    /** Where the operator the source wrote becomes the language's: the one place a connective is
     *  named to be handed on, and no question is asked of it. */
    private static final Set<String> NAMES_ONE = Set.of(
            "souther/compiler/check/Resolve#binOp");

    @Test
    void aConnectiveIsNamedOnlyInATableOfEveryOperator() {
        List<String> found = new ArrayList<>();
        for (ClassModel each : CompiledOutputs.ofWhatThisRepositoryPublishes().all()) {
            String name = each.thisClass().asInternalName();
            if (!OWNERS.contains(name.replaceFirst("\\$.*", ""))) {
                found.addAll(namingsIn(each));
            }
        }
        found.removeIf(NAMES_ONE::contains);
        assertEquals(List.of(), found,
                "ask the operator when its right side runs, or ConditionJoin what it joins,"
                        + " rather than which connective it is; a switch naming one names every"
                        + " operator");
    }

    /** And each way of telling a connective apart for itself is found, so the empty answer above
     *  means something. */
    @Test
    void eachWayOfTellingAConnectiveApartIsFound() {
        String outer = WhatAnOperatorDoesWithItsTwoSidesIsAskedOfTheOperatorTest.class.getName()
                .replace('.', '/');
        List<String> found = new ArrayList<>();
        for (Class<?> fixture : List.of(Comparing.class, Aliasing.class, SwitchingOnSome.class,
                MatchingOnSome.class)) {
            found.addAll(namingsIn(classOf(fixture.getName().replace('.', '/'))));
        }
        // A switch's table is kept in a class javac makes beside the outermost one.
        found.addAll(namingsIn(classOf(outer + "$1")));
        assertEquals(new TreeSet<>(List.of(
                        outer + "$Comparing#stopsEarly",
                        outer + "$Aliasing#conjoins",
                        outer + "$MatchingOnSome#conjoins",
                        outer + "$1 names some operators and not every one")),
                new TreeSet<>(found));
    }

    static final class Comparing {
        static boolean stopsEarly(BinOp op) {
            return op == BinOp.AND || op == BinOp.OR;
        }
    }

    static final class Aliasing {
        static boolean conjoins(BinOp op) {
            BinOp target = BinOp.AND;
            return op.equals(target);
        }
    }

    static final class SwitchingOnSome {
        static boolean conjoins(BinOp op) {
            return switch (op) {
                case AND -> true;
                default -> false;
            };
        }
    }

    static final class MatchingOnSome {
        static boolean conjoins(Object value) {
            return switch (value) {
                case BinOp.AND -> true;
                default -> false;
            };
        }
    }

    private static ClassModel classOf(String internalName) {
        Optional<ClassModel> found = CompiledOutputs.ofEverythingCompiledHere().find(internalName);
        assertTrue(found.isPresent(), internalName + " is compiled here");
        return found.get();
    }

    /**
     * Every method of {@code model} that names a connective other than for a switch's table, every
     * pattern switch naming one and not every operator, and the class itself where the switch
     * tables it builds name one and not every operator.
     */
    private static List<String> namingsIn(ClassModel model) {
        String name = model.thisClass().asInternalName();
        Set<String> out = new TreeSet<>();
        Set<String> tabled = new TreeSet<>();
        for (MethodModel method : model.methods()) {
            Optional<CodeModel> code = method.code();
            if (code.isEmpty()) {
                continue;
            }
            String where = name + "#" + method.methodName().stringValue();
            String read = null;
            for (CodeElement element : code.get()) {
                if (!(element instanceof Instruction instruction)) {
                    continue;
                }
                if (read != null) {
                    if (instruction instanceof InvokeInstruction invoke
                            && invoke.owner().asInternalName().equals(OPERATOR)
                            && invoke.name().stringValue().equals("ordinal")) {
                        tabled.add(read);
                    } else if (CONNECTIVES.contains(read)) {
                        out.add(where);
                    }
                    read = null;
                }
                if (instruction instanceof FieldInstruction field
                        && field.opcode() == Opcode.GETSTATIC
                        && field.owner().asInternalName().equals(OPERATOR)
                        && EVERY_OPERATOR.contains(field.name().stringValue())) {
                    read = field.name().stringValue();
                } else if (instruction instanceof InvokeDynamicInstruction dynamic
                        && dynamic.bootstrapMethod().owner().descriptorString()
                                .equals("L" + SWITCHES + ";")) {
                    Set<String> matched = operatorsAmong(dynamic.bootstrapArgs());
                    if (namesSomeConnectiveAndNotEveryOperator(matched)) {
                        out.add(where);
                    }
                }
            }
        }
        if (namesSomeConnectiveAndNotEveryOperator(tabled)) {
            out.add(name + " names some operators and not every one");
        }
        return new ArrayList<>(out);
    }

    private static boolean namesSomeConnectiveAndNotEveryOperator(Set<String> named) {
        return named.stream().anyMatch(CONNECTIVES::contains) && !named.containsAll(EVERY_OPERATOR);
    }

    /**
     * The operators a pattern switch's labels name. A label naming a constant of an enum is one
     * worked out where the switch is first run, made of the enum's class and the constant's name,
     * so it is read off what it is made of.
     */
    private static Set<String> operatorsAmong(List<ConstantDesc> labels) {
        Set<String> out = new TreeSet<>();
        for (ConstantDesc label : labels) {
            List<ConstantDesc> parts = new ArrayList<>();
            partsOf(label, parts);
            boolean ofTheOperator = parts.stream().anyMatch(part ->
                    part.equals(BinOp.class.getName())
                            || (part instanceof ClassDesc type
                                    && type.descriptorString().equals("L" + OPERATOR + ";")));
            if (ofTheOperator) {
                parts.forEach(part -> {
                    if (part instanceof String text && EVERY_OPERATOR.contains(text)) {
                        out.add(text);
                    }
                });
            }
        }
        return out;
    }

    private static void partsOf(ConstantDesc constant, List<ConstantDesc> out) {
        out.add(constant);
        if (constant instanceof DynamicConstantDesc<?> made) {
            out.add(made.constantType());
            made.bootstrapArgsList().forEach(each -> partsOf(each, out));
        }
    }

    private static Set<String> everyOperator() {
        Set<String> out = new TreeSet<>();
        for (BinOp each : BinOp.values()) {
            out.add(each.name());
        }
        return Set.copyOf(out);
    }
}
