package souther.architecture;

import souther.compiler.inputs.MadeFrom;
import souther.compiler.inputs.ValuesAt;
import souther.compiler.inputs.ValuesHeld;

import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassModel;
import java.lang.classfile.constantpool.MemberRefEntry;
import java.lang.classfile.constantpool.PoolEntry;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An answer of what an expression is to a place is made where that relation is read, and nowhere
 * else.
 *
 * <p>{@link ValuesAt} says an expression is the values at a place, {@link ValuesHeld} that it holds
 * them in the way a count or an order needs, {@link MadeFrom} that it was worked out of them. The
 * arms are records, so any class can write one with the place of another: a reader with a
 * {@code MadeFrom.FromOne} could say {@code new ValuesAt.At(from.place())}, and a rule would be filed at
 * a place whose values are not the ones it is about. javac does not refuse that, and the types are
 * only as good as who can make them.
 *
 * <p>Read off the compiled classes, because it is a rule about who calls what: a constructor named
 * is in the constant pool of the class that names it, however the call is written. What is refused
 * is a crossing out of {@code souther.compiler.inputs}, which owns the walks that read each relation.
 */
class AnAnswerOfARelationIsMadeOnlyWhereTheRelationIsReadTest {

    /** The one package that reads where an expression stands, and says it. */
    private static final String OWNER = "souther/compiler/inputs/";

    private static final CompiledOutputs PUBLISHED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    @Test
    void noClassOutsideTheOwnerMakesOne() {
        List<String> making = new ArrayList<>();
        for (ClassModel each : PUBLISHED.all()) {
            if (!each.thisClass().asInternalName().startsWith(OWNER) && makesOne(each)) {
                making.add(each.thisClass().asInternalName());
            }
        }

        assertEquals(List.of(), making.stream().sorted().toList(),
                "an answer of one relation made from the place of another says what was not read:"
                        + " ask the reading for the relation wanted, from InputReads");
    }

    /** The control: the owner makes them, which is what this reads. */
    @Test
    void andTheCheckSeesTheOwnerMakingThem() {
        assertFalse(arms().isEmpty(), "the arms are read off the types");
        assertTrue(PUBLISHED.all().stream()
                        .filter(each -> each.thisClass().asInternalName().startsWith(OWNER))
                        .anyMatch(AnAnswerOfARelationIsMadeOnlyWhereTheRelationIsReadTest::makesOne),
                "the reading of the inputs makes the answers it hands out");
    }

    /** The internal names of the arms of the three answers. */
    private static Set<String> arms() {
        Set<String> names = new LinkedHashSet<>();
        for (Class<?> type : List.of(ValuesAt.class, ValuesHeld.class, MadeFrom.class)) {
            for (Class<?> arm : type.getPermittedSubclasses()) {
                names.add(arm.getName().replace('.', '/'));
            }
        }
        return names;
    }

    /** Whether {@code compiled} calls a constructor of one of the arms. */
    private static boolean makesOne(ClassModel compiled) {
        Set<String> arms = arms();
        for (PoolEntry entry : compiled.constantPool()) {
            if (entry instanceof MemberRefEntry member
                    && member.name().stringValue().equals("<init>")
                    && arms.contains(member.owner().name().stringValue())) {
                return true;
            }
        }
        return false;
    }
}
