package souther.architecture;

import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassModel;
import java.lang.classfile.CodeElement;
import java.lang.classfile.CodeModel;
import java.lang.classfile.Instruction;
import java.lang.classfile.MethodModel;
import java.lang.classfile.instruction.ConstantInstruction;
import java.lang.classfile.instruction.InvokeInstruction;
import java.lang.classfile.instruction.NewMultiArrayInstruction;
import java.lang.classfile.instruction.NewPrimitiveArrayInstruction;
import java.lang.classfile.instruction.NewReferenceArrayInstruction;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * In the run time, elements are gathered into one host array only at the call sites below, each of
 * which says why what it gathers is short.
 *
 * <p>A {@code List}, {@code Map} or {@code Set} holds as many elements as its size counts, and none
 * of them keeps its elements in one array, because a VM refuses an array a few elements short of
 * that whatever its heap. An operation that copied a collection into one — an {@code ArrayList},
 * {@code toArray}, {@code List.copyOf}, a host sort, or an array made at a length the code works out
 * rather than writes — would refuse a collection the language holds
 * for want of an intermediate it chose (spec
 * §an-operation-refuses-only-what-its-own-answer-has-no-place-for). What the run time builds with
 * instead is a {@code PersistentVector.Builder}, and {@code Sorting} for an order.
 *
 * <p>A row names the method and the member it calls, by name and descriptor, because the reason is
 * that call's.
 */
class WhoMayHoldElementsInOneArrayTest {

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    /** What gathers elements into one array: a host list that is one, and the calls that make one. */
    private static final Set<String> MAKES_ONE_ARRAY = Set.of(
            "toArray", "copyOf", "copyOfRange", "sort", "toList", "asList");

    /**
     * The call sites that gather into one array, and why each is short. Every reason is a bound on
     * the length, never what building that length would cost.
     *
     * <p>As long as a trie node or a few more: the nodes {@code PersistentHashMap.BitmapIndexedNode}
     * copies, and the tail {@code PersistentVector.Builder.build} copies. As long as a chunk or the
     * count of them: {@code Sorting.Slots}. As long as the terms a caller writes:
     * {@code ExactOrder.allWrittenOut}. As long as a table the class decodes when it is loaded, or an
     * enumeration: {@code CaseTables}, {@code NormalizationTables}, {@code Normalization}'s static
     * initializer, the switch map {@code ExactRounding} is compiled with. As long as one code point's
     * decomposition: {@code Normalization.decomposeOne}. As long as the code points of one
     * {@code String}, which is no longer than a {@code String} holds: {@code Strings.mapCase}. As long
     * as the marks of one combining run of such a string, since no mark that decomposes stands in
     * one ({@code AMarkThatDecomposesIsNeverItsOwnNfcTest}): {@code Normalization.Composing}. As long
     * as a host list the members of an external form already arrived in, which may hold {@code null}
     * that no {@code List} of the language holds: {@code Representations.sortedMembers}.
     */
    private static final List<String> MAY_HOLD_ONE_ARRAY = List.of(
            "souther/exact/ExactOrder#allWrittenOut new java/math/BigInteger[]",
            "souther/exact/ExactRounding$1#<clinit> new I[]",
            "souther/runtime/CaseTables#decodeMapping new I[]",
            "souther/runtime/CaseTables#decodeMapping new [I[]",
            "souther/runtime/CaseTables#decodeRanges new I[]",
            "souther/runtime/PersistentHashMap$BitmapIndexedNode#copyAndInsertValue new java/lang/Object[]",
            "souther/runtime/PersistentHashMap$BitmapIndexedNode#copyAndMigrateInlineToNode"
                    + " new java/lang/Object[]",
            "souther/runtime/PersistentHashMap$BitmapIndexedNode#copyAndMigrateNodeToInline"
                    + " new java/lang/Object[]",
            "souther/runtime/PersistentHashMap$BitmapIndexedNode#copyAndRemoveNode new java/lang/Object[]",
            "souther/runtime/PersistentHashMap$BitmapIndexedNode#copyAndRemoveValue new java/lang/Object[]",
            "souther/runtime/PersistentVector$Builder#build"
                    + " java/util/Arrays.copyOf([Ljava/lang/Object;I)[Ljava/lang/Object;",
            "souther/runtime/Representations#sortedMembers"
                    + " java/util/ArrayList.<init>(Ljava/util/Collection;)V",
            "souther/runtime/Representations#sortedMembers"
                    + " java/util/List.sort(Ljava/util/Comparator;)V",
            "souther/runtime/Sorting$Slots#<init> new [Ljava/lang/Object;[]",
            "souther/runtime/Sorting$Slots#<init> new java/lang/Object[]",
            "souther/runtime/Strings#mapCase java/util/stream/IntStream.toArray()[I",
            "souther/unicode/Normalization#<clinit> java/util/stream/IntStream.toArray()[I",
            "souther/unicode/Normalization#<clinit> java/util/stream/LongStream.toArray()[J",
            "souther/unicode/Normalization#decomposeOne java/util/stream/IntStream.toArray()[I",
            "souther/unicode/Normalization$Composing#holdMark java/util/Arrays.copyOf([II)[I",
            "souther/unicode/Normalization$Composing#order new I[]",
            "souther/unicode/NormalizationTables#decodeIntValues new I[]",
            "souther/unicode/NormalizationTables#decodeMapping new I[]",
            "souther/unicode/NormalizationTables#decodeMapping new [I[]");

    @Test
    void everyRunTimeCallThatHoldsElementsInOneArrayIsWrittenDownHere() {
        assertEquals(MAY_HOLD_ONE_ARRAY, holdingOneArray(),
                "a collection holds more than one array does; gather its elements into a"
                        + " PersistentVector.Builder, or sort them through Sorting");
    }

    private static List<String> holdingOneArray() {
        Set<String> out = new TreeSet<>();
        for (ClassModel each : COMPILED.classesOf(COMPILED.module("souther-runtime"))) {
            for (MethodModel method : each.methods()) {
                String site = each.thisClass().asInternalName() + "#"
                        + method.methodName().stringValue();
                for (CodeModel code : method.code().stream().toList()) {
                    boolean lengthWritten = false;
                    for (CodeElement element : code) {
                        if (element instanceof InvokeInstruction invoke && makesOneArray(invoke)) {
                            out.add(site + " " + invoke.owner().asInternalName() + "."
                                    + invoke.name().stringValue() + invoke.type().stringValue());
                        }
                        arrayMadeAtALengthWorkedOut(element, lengthWritten)
                                .ifPresent(made -> out.add(site + " new " + made));
                        if (element instanceof Instruction) {
                            lengthWritten = element instanceof ConstantInstruction;
                        }
                    }
                }
            }
        }
        return new ArrayList<>(out);
    }

    /**
     * The component type of the array {@code element} makes, where it makes one whose length is
     * worked out rather than written: an array of a written length — the arguments of a call, a
     * pair — is as long as the code says, whatever it holds. A multi-dimensional array is never of
     * a written length here, since only its last dimension is the one pushed last.
     */
    private static Optional<String> arrayMadeAtALengthWorkedOut(
            CodeElement element, boolean lengthWritten) {
        return switch (element) {
            case NewReferenceArrayInstruction array when !lengthWritten ->
                    Optional.of(array.componentType().asInternalName() + "[]");
            case NewPrimitiveArrayInstruction array when !lengthWritten ->
                    Optional.of(array.typeKind().upperBound().descriptorString() + "[]");
            case NewMultiArrayInstruction array -> Optional.of(array.arrayType().asInternalName());
            default -> Optional.empty();
        };
    }

    private static boolean makesOneArray(InvokeInstruction invoke) {
        String owner = invoke.owner().asInternalName();
        String name = invoke.name().stringValue();
        return owner.startsWith("java/util/")
                && (MAKES_ONE_ARRAY.contains(name)
                        || (owner.equals("java/util/ArrayList") && name.equals("<init>")));
    }
}
