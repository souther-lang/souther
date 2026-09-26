package souther.architecture;

import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassModel;
import java.lang.classfile.CodeElement;
import java.lang.classfile.CodeModel;
import java.lang.classfile.MethodModel;
import java.lang.classfile.instruction.InvokeInstruction;
import java.util.ArrayList;
import java.util.List;
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
 * {@code toArray}, {@code List.copyOf}, a host sort — would refuse a collection the language holds
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
     * The call sites that gather into one array, and why each is short.
     *
     * <p>{@code PersistentVector.Builder.build} copies its tail, which is never longer than a trie
     * node. {@code HashCollisionNode.put} holds the keys that share one hash; that many keys cost a
     * copy of all of them per key added, so a node long enough to reach an array's bound is not one a
     * run gets to build. {@code Strings.mapCase} holds the code points of one {@code String}, which
     * is no longer than a {@code String} holds. {@code Normalization} holds one stretch of text, its
     * decomposition, and, while the class is loaded, its own tables.
     * {@code Representations.sortedMembers} copies and sorts the members of an external form, which
     * arrived as one host list and may hold {@code null}; the copy is as long as that list.
     */
    private static final List<String> MAY_HOLD_ONE_ARRAY = List.of(
            "souther/runtime/PersistentHashMap$HashCollisionNode#put"
                    + " java/util/Arrays.copyOf([Ljava/lang/Object;I)[Ljava/lang/Object;",
            "souther/runtime/PersistentVector$Builder#build"
                    + " java/util/Arrays.copyOf([Ljava/lang/Object;I)[Ljava/lang/Object;",
            "souther/runtime/Representations#sortedMembers"
                    + " java/util/ArrayList.<init>(Ljava/util/Collection;)V",
            "souther/runtime/Representations#sortedMembers"
                    + " java/util/List.sort(Ljava/util/Comparator;)V",
            "souther/runtime/Strings#mapCase java/util/stream/IntStream.toArray()[I",
            "souther/unicode/Normalization#<clinit> java/util/stream/IntStream.toArray()[I",
            "souther/unicode/Normalization#<clinit> java/util/stream/LongStream.toArray()[J",
            "souther/unicode/Normalization#canonicalCompose java/util/Arrays.copyOf([II)[I",
            "souther/unicode/Normalization#canonicalDecompose java/util/stream/IntStream.toArray()[I",
            "souther/unicode/Normalization#nfcWithin java/util/stream/IntStream.toArray()[I");

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
                for (CodeModel code : method.code().stream().toList()) {
                    for (CodeElement element : code) {
                        if (element instanceof InvokeInstruction invoke && makesOneArray(invoke)) {
                            out.add(each.thisClass().asInternalName() + "#"
                                    + method.methodName().stringValue() + " "
                                    + invoke.owner().asInternalName() + "."
                                    + invoke.name().stringValue() + invoke.type().stringValue());
                        }
                    }
                }
            }
        }
        return new ArrayList<>(out);
    }

    private static boolean makesOneArray(InvokeInstruction invoke) {
        String owner = invoke.owner().asInternalName();
        String name = invoke.name().stringValue();
        return owner.startsWith("java/util/")
                && (MAKES_ONE_ARRAY.contains(name)
                        || owner.equals("java/util/ArrayList") && name.equals("<init>"));
    }
}
