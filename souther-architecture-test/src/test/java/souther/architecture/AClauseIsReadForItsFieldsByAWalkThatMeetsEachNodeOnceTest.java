package souther.architecture;

import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassModel;
import java.lang.classfile.MethodModel;
import java.lang.classfile.instruction.InvokeInstruction;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The fields a record's rule reads are found by a walk that meets each node of the rule once.
 *
 * <p>A rule that names a value twice holds one node in two slots, so a chain of them is a graph with
 * a path to a node for every way down, and a walk that goes down every slot of every node makes a
 * number of visits that doubles with each link. Which fields a rule reads is a set, so no visit
 * after the first adds one. Asked as a time, this takes a clause the slow walk cannot finish and a
 * test that leaves the process running when it gives up; asked of the class, it is what the reader
 * calls.
 */
class AClauseIsReadForItsFieldsByAWalkThatMeetsEachNodeOnceTest {

    private static final String CORE = "souther/compiler/core/Core";

    private static final String READER = "souther/compiler/check/RecordRules";

    private static final CompiledOutputs PUBLISHED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    @Test
    void theReaderGoesDownThroughTheWalkThatMeetsEachNodeOnce() {
        Set<String> called = new TreeSet<>();
        for (ClassModel owner : PUBLISHED.all()) {
            if (!owner.thisClass().asInternalName().equals(READER)) {
                continue;
            }
            WhereALambdaIsWritten lambdas = WhereALambdaIsWritten.in(owner);
            String reader = AMethod.of(READER, "readFrom",
                    "(L" + CORE + ";Ljava/util/Map;Ljava/util/Set;)V");
            for (MethodModel method : owner.methods()) {
                if (method.code().isEmpty()
                        || !lambdas.enclosing(AMethod.of(owner, method)).equals(reader)) {
                    continue;
                }
                for (var element : method.code().orElseThrow()) {
                    if (element instanceof InvokeInstruction call) {
                        called.add(call.owner().asInternalName() + "#" + call.name().stringValue());
                    }
                }
            }
        }

        assertTrue(called.contains(CORE + "#forEachDistinctNode"),
                "RecordRules.readFrom was found calling " + called);
        Set<String> goingDownEverySlot = new TreeSet<>(called);
        goingDownEverySlot.retainAll(Set.of(CORE + "#forEachChild", CORE + "#mapAll",
                CORE + "#mapChildren", READER + "#readFrom"));
        assertEquals(Set.of(), goingDownEverySlot,
                "a set of fields is found by meeting each node once: a walk down every slot of"
                        + " every node makes a visit for each path to a node");
    }
}
