package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.lang.classfile.ClassFile;
import java.lang.classfile.ClassModel;
import java.lang.classfile.CodeModel;
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
 * The rules reaching a behavior's input are read again, with a position settled, in one place.
 *
 * <p>Asking what the declarations leave once something is fixed is what every search over an input
 * needs, and each one that reached for it directly brought its own way of naming a position and its
 * own walk to find them. Three of them did: a record composed field by field, a parameter chosen a
 * position at a time, and a form solved for a level — and the third never found the capability at
 * all and walked the box around the positions instead, which is a set the rules have a corner cut
 * out of. That is the shape {@link Quantities} exists to stop, and it stops it only while the way
 * round it is closed.
 *
 * <p><b>Read off the compiled classes.</b> What is checked is who calls the conditioning factory,
 * which no way of spelling the call can dress up as something else.
 *
 * <p><b>Both directions.</b> A check that only counts trespassers passes when it reads nothing at
 * all, so what is expected to be found is named as well.
 *
 * <p><b>The list below is what has not been moved yet, and not a list of exceptions.</b> Two callers
 * remain, and both want a second answer of the same reading — how much a position must hold, beside
 * where its values run — which is a question this boundary does not carry today. Striking one off is
 * what moving it looks like; adding one is a third way round the boundary and fails here.
 */
class OnlyTheReadingOfAnInputConditionsItsDeclarationsTest {

    private static final String CONDITIONS = "souther.compiler.check.FieldDomains";

    /** Who may read the declarations again with a position settled. */
    private static final Set<String> MAY_CONDITION = Set.of(
            // The reading of an input, which is what the boundary is.
            "souther.compiler.inputs.PlacedRules",
            // A record composed field by field, which also asks how much each field must hold.
            "souther.compiler.partition.Partitions",
            // A parameter chosen a position at a time, which asks the same second question and
            // walks the positions itself.
            "souther.compiler.partition.Generator");

    @Test
    void nothingElseReadsTheDeclarationsAgainWithAPositionSettled() throws IOException {
        Set<String> found = new TreeSet<>();
        for (Path each : classes()) {
            ClassModel model = ClassFile.of().parse(Files.readAllBytes(each));
            String from = nestOf(model.thisClass().asInternalName().replace('/', '.'));
            if (from.equals(CONDITIONS)) {
                continue;   // what the reading does with itself is its own business
            }
            for (var method : model.methods()) {
                CodeModel code = method.code().orElse(null);
                if (code == null) {
                    continue;
                }
                for (var element : code) {
                    if (element instanceof InvokeInstruction call
                            && call.owner().asInternalName().replace('/', '.').equals(CONDITIONS)
                            && conditions(call.name().stringValue(), call.typeSymbol())) {
                        found.add(from);
                    }
                }
            }
        }
        assertFalse(found.isEmpty(), "nothing reads the declarations again at all; this check is "
                + "reading no calls");
        assertEquals(new TreeSet<>(MAY_CONDITION), found,
                "who reads a value's declarations again with one of its positions settled");
    }

    /**
     * Which of the reading's members hand back a reading conditioned on an assignment.
     *
     * <p>Told apart by what they take and not by their name. Reading a declaration and reading it
     * again with a position settled are both called {@code of}, and the second is the one that takes
     * the settlings — so a check on the name alone would report every reader of a declaration as one
     * that conditions it.
     */
    private static boolean conditions(String member, java.lang.constant.MethodTypeDesc taken) {
        if (member.equals("given")) {
            return true;
        }
        return member.equals("of") && taken.parameterCount() > 0
                && taken.parameterType(taken.parameterCount() - 1).displayName().equals("Map");
    }

    /** The nest a class belongs to: a lambda written inside a reader is that reader. */
    private static String nestOf(String binaryName) {
        int nested = binaryName.indexOf('$');
        return nested < 0 ? binaryName : binaryName.substring(0, nested);
    }

    private static List<Path> classes() throws IOException {
        Path root = Path.of("target", "classes").toAbsolutePath();
        try (Stream<Path> walk = Files.walk(root)) {
            return new ArrayList<>(new LinkedHashSet<>(
                    walk.filter(each -> each.toString().endsWith(".class")).toList()));
        }
    }
}
