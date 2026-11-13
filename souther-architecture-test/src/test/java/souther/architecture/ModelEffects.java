package souther.architecture;

import java.lang.classfile.ClassModel;
import java.lang.classfile.CodeElement;
import java.lang.classfile.MethodModel;
import java.lang.classfile.instruction.InvokeDynamicInstruction;
import java.lang.classfile.instruction.InvokeInstruction;
import java.lang.reflect.AccessFlag;
import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

/**
 * What the methods of the compiled classes do to a model, worked out from the classes.
 *
 * <p>Which calls read what a model says and which change what it is made of is a fact about the
 * code, and a list of names kept beside it is a list that is wrong the day a method is added or
 * the body of one is changed. What is said by hand is the store's own operations
 * ({@link ModelVocabulary}), and everything above them follows: a method reads a report if it can
 * reach {@code Db.allReports}, and changes a model if it can reach one of the store's changes or
 * hands back another model.
 *
 * <p>The store's own methods are the end of the working out and not a part of it: they change and
 * read what they hold as part of answering, and what a caller does to a model is what it calls on
 * the store from outside it.
 *
 * <p>A method can reach a call it makes, and every method that call may run: those of the classes
 * below the one the call names that declare the same method, and the body of a lambda whose
 * functional method it is. A lambda that is made is taken to run, because it may be handed to code
 * that is not among these classes. The classes are all of the repository's, so what is not
 * followed is only what is outside it.
 */
final class ModelEffects {

    private final Map<String, Set<String>> implementers;

    private final Set<String> withCode;

    private final Set<String> changers;

    private final Set<String> reportReaders;

    private ModelEffects(Map<String, Set<String>> implementers, Set<String> withCode,
                         Set<String> changers, Set<String> reportReaders) {
        this.implementers = implementers;
        this.withCode = withCode;
        this.changers = changers;
        this.reportReaders = reportReaders;
    }

    /** The effects of the methods of {@code classes}, as {@link AMethod} says them. */
    static ModelEffects of(Collection<ClassModel> classes) {
        Map<String, ClassModel> byName = new HashMap<>();
        for (ClassModel each : classes) {
            byName.put(each.thisClass().asInternalName(), each);
        }
        Map<String, Set<String>> supers = new HashMap<>();
        for (ClassModel each : classes) {
            supers.put(each.thisClass().asInternalName(), supertypesOf(each, byName));
        }
        Map<String, Set<String>> implementers = new HashMap<>();
        Set<String> withCode = new HashSet<>();
        for (ClassModel each : classes) {
            String owner = each.thisClass().asInternalName();
            for (MethodModel method : each.methods()) {
                if (method.code().isPresent()) {
                    withCode.add(AMethod.of(each, method));
                }
                if (overridable(method)) {
                    String self = AMethod.of(each, method);
                    for (String above : supers.get(owner)) {
                        implementers.computeIfAbsent(AMethod.of(above,
                                method.methodName().stringValue(),
                                method.methodType().stringValue()), k -> new HashSet<>())
                                .add(self);
                    }
                }
            }
        }
        Map<String, Set<String>> calledBy = new HashMap<>();
        Set<String> changing = new HashSet<>();
        Set<String> reading = new HashSet<>();
        Set<String> answering = new HashSet<>();
        for (ClassModel each : classes) {
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
                            boolean fromOutside = !each.thisClass().asInternalName()
                                    .equals(ModelVocabulary.DB);
                            if (fromOutside && owner.equals(ModelVocabulary.DB)
                                    && ModelVocabulary.DB_CHANGES.contains(name)) {
                                changing.add(self);
                            }
                            if (fromOutside && owner.equals(ModelVocabulary.DB)
                                    && ModelVocabulary.DB_READS_A_REPORT.contains(name)) {
                                reading.add(self);
                            }
                            if (owner.equals(ModelVocabulary.COMPILATION)
                                    && ModelVocabulary.ANSWERS.contains(name)) {
                                answering.add(self);
                            }
                            String callee = AMethod.of(owner, name, call.type().stringValue());
                            calledBy.computeIfAbsent(callee, k -> new HashSet<>()).add(self);
                            for (String target : implementers.getOrDefault(callee, Set.of())) {
                                calledBy.computeIfAbsent(target, k -> new HashSet<>()).add(self);
                            }
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
        for (ClassModel each : classes) {
            for (MethodModel method : each.methods()) {
                if (method.code().isPresent() && !method.flags().has(AccessFlag.STATIC)
                        && each.thisClass().asInternalName().equals(ModelVocabulary.COMPILATION)) {
                    if (method.methodTypeSymbol().returnType().descriptorString()
                            .equals(ModelVocabulary.COMPILATION_TYPE)) {
                        changing.add(AMethod.of(each, method));
                    }
                    if (ModelVocabulary.ANSWERS.contains(method.methodName().stringValue())) {
                        answering.add(AMethod.of(each, method));
                    }
                    if (ModelVocabulary.SAYS_WITHOUT_REPORTS
                            .contains(method.methodName().stringValue())) {
                        reading.add(AMethod.of(each, method));
                    }
                }
            }
        }
        Set<String> readers = close(reading, calledBy);
        readers.removeAll(close(answering, calledBy));
        return new ModelEffects(implementers, withCode, close(changing, calledBy), readers);
    }

    /** The methods the call of {@code callee} may run: itself and what is declared below it. */
    Set<String> targets(String callee) {
        Set<String> found = new HashSet<>(implementers.getOrDefault(callee, Set.of()));
        found.add(callee);
        return found;
    }

    /** Whether {@code method} has a body among the classes. */
    boolean hasCode(String method) {
        return withCode.contains(method);
    }

    /** Whether the method can reach a change to a model, or hands back another. */
    boolean changes(String method) {
        return changers.contains(method);
    }

    /** Whether the method can reach a read of the reports a store holds. */
    boolean readsReports(String method) {
        return reportReaders.contains(method);
    }

    Set<String> changers() {
        return Set.copyOf(changers);
    }

    private static Set<String> close(Set<String> seeds, Map<String, Set<String>> calledBy) {
        Set<String> reached = new HashSet<>(seeds);
        Deque<String> work = new ArrayDeque<>(seeds);
        while (!work.isEmpty()) {
            for (String caller : calledBy.getOrDefault(work.poll(), Set.of())) {
                if (reached.add(caller)) {
                    work.add(caller);
                }
            }
        }
        return reached;
    }

    private static boolean overridable(MethodModel method) {
        String name = method.methodName().stringValue();
        return !method.flags().has(AccessFlag.STATIC) && !method.flags().has(AccessFlag.PRIVATE)
                && !name.startsWith("<");
    }

    private static Set<String> supertypesOf(ClassModel each, Map<String, ClassModel> byName) {
        Set<String> found = new HashSet<>();
        Deque<ClassModel> work = new ArrayDeque<>();
        work.add(each);
        while (!work.isEmpty()) {
            ClassModel at = work.poll();
            Set<String> direct = new HashSet<>();
            at.superclass().ifPresent(parent -> direct.add(parent.asInternalName()));
            at.interfaces().forEach(parent -> direct.add(parent.asInternalName()));
            for (String parent : direct) {
                if (found.add(parent) && byName.containsKey(parent)) {
                    work.add(byName.get(parent));
                }
            }
        }
        return found;
    }
}
