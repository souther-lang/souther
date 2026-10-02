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
 * Where a count reads a declaration's rules.
 *
 * <p>A count asks a declaration's rules three things — whether they leave anything, how many whole
 * numbers they leave at a place, which sizes they leave a collection there — and under a supposing
 * all three are about the rules as that supposing reads them: nothing under a name supposed to have
 * a value, and a newtype that writes nothing read as the one beneath. What hands those readings out
 * is the supposing ({@code Supposing#readingOf}), and a count asking any of the three of anything
 * else reads the declaration's own rules, including the ones the supposing was about. Every reader
 * would still be answering, and the answer would be a count of a world nobody supposed.
 *
 * <p>No comparison of answers can hold this. A test setting the readings a supposing shares beside
 * readings made for each declaration alone runs both through the same count, so a count that read
 * past the supposing reads past it on both sides. What holds it is which methods of the count reach
 * a reading of a declaration's rules by the declaration's name, and the rows below are those.
 *
 * <p>The count is the classes that make one — the rising, the step it takes per declaration, and
 * the supposing — with whatever is nested in them; a lambda is answered for as the method it is
 * written in. A method handed to something that will call it reaches a reading as surely as calling
 * it, so a handle among a bootstrap's arguments is read as a call.
 *
 * <p>Named rather than counted, which is what stands in for a control: a walk that stopped reading
 * instructions comes back with nothing, and nothing is not what this expects.
 */
class ACountReadsADeclarationsRulesThroughWhatItSupposesTest {

    private static final String CHECK = "souther/compiler/check/";

    /** The classes a count is made by, each with whatever is nested in it. */
    private static final List<String> THE_COUNT = List.of(
            CHECK + "TypeCardinality", CHECK + "CardinalityTransfer", CHECK + "Supposing");

    private static final String A_NAME = "Lsouther/compiler/types/TypeSymbol$AtModule;";
    private static final String A_WORLD = "L" + CHECK + "RuleReadingContext;";

    private static final List<String> READING_BY_NAME = List.of(
            // A supposing's own readings: under it, or the declaration's own where it stops nowhere.
            AMethod.of(CHECK + "Supposing", "readingOf",
                    "(" + A_NAME + A_WORLD + ")L" + CHECK + "DeclarationReading;")
                    + " -> " + CHECK + "InvariantChecker#readFields",
            AMethod.of(CHECK + "Supposing$Across", "ownReadingOf",
                    "(" + A_NAME + A_WORLD + ")L" + CHECK + "DeclarationReading;")
                    + " -> " + CHECK + "InvariantChecker#readFields",
            // What a declaration settles before any rising, which is the counts its rules ask about
            // and is the same whatever is supposed beside it.
            AMethod.of(CHECK + "TypeCardinality$Premises", "read",
                    "(" + A_WORLD + ")L" + CHECK + "TypeCardinality$Premises;")
                    + " -> " + CHECK + "CardinalityPremise#of");

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    @Test
    void everyMethodOfACountThatReadsADeclarationsRulesIsWrittenDown() {
        Set<String> found = readingByName();
        assertEquals(READING_BY_NAME, List.copyOf(found),
                () -> "the methods of a count that read a declaration's rules are not the ones"
                        + " written down.\n  found: " + found + "\n  written down: "
                        + READING_BY_NAME + "\nAsk the supposing the count is under for the"
                        + " reading, or say here why this method reads the rules whatever is"
                        + " supposed.");
    }

    /** Every method of the count reaching a reading by name, as the method and what it reached. */
    private static Set<String> readingByName() {
        Set<String> found = new TreeSet<>();
        for (ClassModel model : COMPILED.all()) {
            if (!ofTheCount(model.thisClass().asInternalName())) {
                continue;
            }
            WhereALambdaIsWritten lambdas = WhereALambdaIsWritten.in(model);
            for (MethodModel method : model.methods()) {
                for (Instruction instruction : instructionsOf(method)) {
                    reached(instruction).ifPresent(reading -> found.add(
                            lambdas.enclosing(AMethod.of(model, method)) + " -> " + reading));
                }
            }
        }
        return found;
    }

    private static boolean ofTheCount(String className) {
        for (String each : THE_COUNT) {
            if (className.equals(each) || className.startsWith(each + "$")) {
                return true;
            }
        }
        return false;
    }

    /**
     * Whether {@code owner}'s {@code name}, taking what {@code descriptor} says, reads a
     * declaration's rules given the declaration: every way into a reading of the rules, and every
     * reader of them that makes its own reading when handed a name rather than a reading.
     */
    private static boolean readsByName(String owner, String name, String descriptor) {
        return switch (owner) {
            case CHECK + "InvariantChecker" -> name.equals("readFields") || name.equals("seedFields");
            case CHECK + "FieldDomains", CHECK + "OccurrenceCounts", CHECK + "OccurrenceValues" ->
                    name.equals("of") && descriptor.startsWith("(" + A_NAME);
            case CHECK + "CardinalityPremise" -> name.equals("of");
            default -> false;
        };
    }

    /** What reading an instruction reaches by name, if any: by calling it, or by handing it over. */
    private static Optional<String> reached(Instruction instruction) {
        return switch (instruction) {
            case InvokeInstruction call -> named(call.owner().name().stringValue(),
                    call.name().stringValue(), call.type().stringValue());
            case InvokeDynamicInstruction handed -> {
                for (LoadableConstantEntry each : handed.invokedynamic().bootstrap().arguments()) {
                    if (each instanceof MethodHandleEntry handle) {
                        MemberRefEntry member = handle.reference();
                        Optional<String> reading = named(member.owner().name().stringValue(),
                                member.name().stringValue(), member.type().stringValue());
                        if (reading.isPresent()) {
                            yield reading;
                        }
                    }
                }
                yield Optional.empty();
            }
            default -> Optional.empty();
        };
    }

    private static Optional<String> named(String owner, String name, String descriptor) {
        return readsByName(owner, name, descriptor)
                ? Optional.of(owner + "#" + name) : Optional.empty();
    }

    private static List<Instruction> instructionsOf(MethodModel method) {
        Optional<CodeModel> code = method.code();
        return code.map(each -> each.elementList().stream()
                .filter(Instruction.class::isInstance)
                .map(Instruction.class::cast)
                .toList()).orElse(List.of());
    }
}
