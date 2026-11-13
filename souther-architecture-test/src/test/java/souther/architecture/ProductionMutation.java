package souther.architecture;

import java.lang.classfile.ClassModel;
import java.lang.classfile.CodeElement;
import java.lang.classfile.MethodModel;
import java.lang.classfile.instruction.InvokeDynamicInstruction;
import java.lang.classfile.instruction.InvokeInstruction;
import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

/**
 * The methods of the compiler's own code that can change a model they are handed.
 *
 * <p>A model handed to code the check does not walk may be changed by it, and a list of the code
 * that does, kept by hand, is a list that is wrong the day somebody writes the next. What changes a
 * model is a few calls, the ones said at {@link ModelVocabulary}, and a method can change one that
 * calls them or calls a method that can, so the methods that can are the ones from which those calls
 * can be reached. Worked out from the compiled classes, by the names a call is written with: a call
 * that is dispatched to another class than the one it names, through an interface or a subclass, is
 * one this does not follow.
 */
final class ProductionMutation {

    private ProductionMutation() { }

    /** The methods of {@code production}, as {@link AMethod} says them, that can change a model. */
    static Set<String> reaching(Collection<ClassModel> production) {
        Map<String, Set<String>> calledBy = new HashMap<>();
        Set<String> changing = new HashSet<>();
        for (ClassModel each : production) {
            for (MethodModel method : each.methods()) {
                if (method.code().isEmpty()) {
                    continue;
                }
                String self = AMethod.of(each, method);
                for (CodeElement element : method.code().get().elementList()) {
                    switch (element) {
                        case InvokeInstruction call -> {
                            String owner = call.owner().asInternalName();
                            String name = call.name().stringValue();
                            if ((owner.equals(ModelVocabulary.DB)
                                    && ModelVocabulary.DB_CHANGES.contains(name))
                                    || (owner.equals(ModelVocabulary.COMPILATION)
                                    && ModelVocabulary.COMPILATION_CHANGES.contains(name))) {
                                changing.add(self);
                            }
                            calledBy.computeIfAbsent(
                                    AMethod.of(owner, name, call.type().stringValue()),
                                    k -> new HashSet<>()).add(self);
                        }
                        case InvokeDynamicInstruction call -> {
                            String impl = ModelWalk.lambdaImplementation(call);
                            if (impl != null) {
                                calledBy.computeIfAbsent(impl, k -> new HashSet<>()).add(self);
                            }
                        }
                        default -> { }
                    }
                }
            }
        }
        Deque<String> work = new ArrayDeque<>(changing);
        while (!work.isEmpty()) {
            for (String caller : calledBy.getOrDefault(work.poll(), Set.of())) {
                if (changing.add(caller)) {
                    work.add(caller);
                }
            }
        }
        return changing;
    }
}
