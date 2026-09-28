package souther.architecture;

import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassModel;
import java.lang.classfile.CodeModel;
import java.lang.classfile.MethodModel;
import java.lang.classfile.instruction.InvokeInstruction;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Where a checked body becomes the body a backend emits.
 *
 * <p>{@code GrowingFold.rewrite} is the one pass between checking and emission, and what it hands
 * out is held to the typing a checked tree is held to by {@code EveryTreeTheBackendIsHandedIsTypedTest}
 * in {@code souther-compiler}. That test reads what each of the queries below hands on — a
 * behavior's body, and the definitions a module's check emits — because there is no one product
 * both come out of. A method that rewrote a body somewhere else would hand the backend a tree that
 * test never reads.
 *
 * <p>A row added here is a body the contract does not reach yet: the test reads it too, and then
 * the row is written down.
 */
class WhoMayRewriteACheckedBodyForTheBackendTest {

    private static final String REWRITE = "souther/compiler/core/GrowingFold";

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    /** The queries whose answers hold a rewritten body, by class: which query hands the body on is
     *  the question, and a lambda one of them rewrites in is compiled into the same class. */
    private static final List<String> REWRITING = List.of(
            "souther/compiler/query/Bodies$CheckedBehavior",
            "souther/compiler/query/Bodies$ModuleCheck");

    @Test
    void everyMethodThatRewritesACheckedBodyIsOneTheContractReads() {
        assertEquals(REWRITING, new ArrayList<>(rewriting()),
                "a class rewriting a checked body for the backend whose answer"
                        + " EveryTreeTheBackendIsHandedIsTypedTest does not read");
    }

    /** Every class outside the pass that calls into it. */
    private static Set<String> rewriting() {
        Set<String> found = new TreeSet<>();
        for (ClassModel model : COMPILED.all()) {
            String owner = model.thisClass().asInternalName();
            if (owner.equals(REWRITE) || owner.startsWith(REWRITE + "$")) {
                continue;
            }
            for (MethodModel method : model.methods()) {
                CodeModel code = method.code().orElse(null);
                if (code == null) {
                    continue;
                }
                for (var element : code) {
                    if (element instanceof InvokeInstruction call
                            && REWRITE.equals(call.owner().asInternalName())
                            && "rewrite".equals(call.name().stringValue())) {
                        found.add(owner);
                    }
                }
            }
        }
        return found;
    }
}
