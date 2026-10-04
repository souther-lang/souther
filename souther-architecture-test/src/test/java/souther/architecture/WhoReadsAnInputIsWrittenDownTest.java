package souther.architecture;

import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassModel;
import java.lang.classfile.CodeModel;
import java.lang.classfile.Instruction;
import java.lang.classfile.MethodModel;
import java.lang.classfile.constantpool.LoadableConstantEntry;
import java.lang.classfile.constantpool.MemberRefEntry;
import java.lang.classfile.constantpool.MethodHandleEntry;
import java.lang.classfile.instruction.InvokeDynamicInstruction;
import java.lang.classfile.instruction.InvokeInstruction;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Where this compiler reads an input, and why each place is entitled to.
 *
 * <p>Reading an input is every rule of every parameter read, and what the reading keeps of the
 * contexts it was asked under is worked out from nothing. A behavior is measured by several
 * questions — its division, the subject a row is written for, the meetings its body holds and the
 * decisions it makes — and each needs its input read. So the reading is work of the revision
 * ({@code AnInputRead}): the first of them reads, and the rest are lent what it read. A measure
 * that read the input for itself would answer the same and cost the reading again, with nothing to
 * say so.
 *
 * <p>What is written down is each production method that reaches the reading, by calling it or by
 * handing it over to be called later. A method that takes what it reads and reads it again here is
 * a row of its own, and so is a reading somebody stopped making: the set is compared whole.
 *
 * <p>The rows are named rather than counted, which is what stands in for a control: a walk that
 * stopped reading instructions comes back with nothing, which is not what this expects.
 */
class WhoReadsAnInputIsWrittenDownTest {

    private static final String INPUTS = "souther/compiler/inputs/";

    private static final String QUERY = "souther/compiler/query/";

    private static final String READ = AMethod.of(INPUTS + "InputDomain", "reading",
            "(Lsouther/compiler/check/RuleReadingSource;)L" + INPUTS + "InputReading;");

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    /**
     * Every method that reads an input, and why.
     *
     * <p>The revision's work, which is where a behavior's own input is read for every measure of
     * it. And the subject a dependency's answer is composed against, which is an input nobody
     * declared — the answer's type, standing as one parameter — read once for the behavior it is
     * composed beside.
     */
    private static final Set<String> READING_AN_INPUT = Set.of(
            AMethod.of(INPUTS + "AnInputRead", "workedOut",
                    "(Lsouther/compiler/revision/RevisionKnowledge;)L" + INPUTS + "InputReading;")
                    + " -> " + READ,
            AMethod.of(QUERY + "Adequacy", "standingFor",
                    "(L" + QUERY + "Db;Ljava/lang/String;Lsouther/compiler/partition/MeasuredInput;"
                            + "Lsouther/compiler/types/Type;)Lsouther/compiler/partition/MeasuredInput;")
                    + " -> " + READ);

    @Test
    void everyMethodThatReadsAnInputIsWrittenDown() {
        Set<String> found = readingAnInput();
        assertEquals(new TreeSet<>(READING_AN_INPUT), found,
                () -> "the methods that read an input are not the ones written down.\n  found: "
                        + found + "\n  written down: " + new TreeSet<>(READING_AN_INPUT)
                        + "\nA measure of a behavior takes the reading the revision made of its"
                        + " input (AnInputRead) rather than reading it again; a reading of some"
                        + " other input is written down here with why.");
    }

    /** Every production method that names the reading, as the method and what it named. */
    private static Set<String> readingAnInput() {
        Set<String> found = new TreeSet<>();
        for (ClassModel model : COMPILED.all()) {
            for (MethodModel method : model.methods()) {
                for (Instruction instruction : instructionsOf(method)) {
                    if (namesTheReading(instruction)) {
                        found.add(AMethod.of(model, method) + " -> " + READ);
                    }
                }
            }
        }
        return found;
    }

    /**
     * Whether an instruction names the reading: by calling it, or by handing it over to be called
     * later, which arrives as a handle among the arguments a bootstrap is given.
     */
    private static boolean namesTheReading(Instruction instruction) {
        return switch (instruction) {
            case InvokeInstruction call -> READ.equals(AMethod.of(
                    call.owner().asInternalName(), call.name().stringValue(), call.typeSymbol()));
            case InvokeDynamicInstruction handed -> {
                for (LoadableConstantEntry each : handed.invokedynamic().bootstrap().arguments()) {
                    if (each instanceof MethodHandleEntry handle) {
                        MemberRefEntry member = handle.reference();
                        String type = member.type().stringValue();
                        if (type.startsWith("(") && READ.equals(AMethod.of(
                                member.owner().asInternalName(), member.name().stringValue(),
                                type))) {
                            yield true;
                        }
                    }
                }
                yield false;
            }
            default -> false;
        };
    }

    private static List<Instruction> instructionsOf(MethodModel method) {
        Optional<CodeModel> code = method.code();
        return code.map(each -> each.elementList().stream()
                .filter(Instruction.class::isInstance)
                .map(Instruction.class::cast)
                .toList()).orElse(List.of());
    }
}
