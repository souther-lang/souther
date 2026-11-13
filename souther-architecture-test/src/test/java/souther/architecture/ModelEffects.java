package souther.architecture;

import java.lang.classfile.Attributes;
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

    private final Map<String, Set<String>> supers;

    private final Set<String> declared;

    private final Set<String> withCode;

    private final Set<String> changers;

    private final Set<String> reportReaders;

    private ModelEffects(Map<String, Set<String>> implementers, Map<String, Set<String>> supers,
                         Set<String> declared, Set<String> withCode, Set<String> changers,
                         Set<String> reportReaders) {
        this.implementers = implementers;
        this.supers = supers;
        this.declared = declared;
        this.withCode = withCode;
        this.changers = changers;
        this.reportReaders = reportReaders;
    }

    /**
     * Every method a call of {@code callee} may run, as {@code owner#name(descriptor)}: itself, the
     * one it is inherited from where the class it names does not declare it, and what is declared
     * below either. A class of the platform is not followed below: what its subclasses in the
     * repository declare is not what a call of its method runs.
     */
    private static Set<String> resolved(String callee, Map<String, Set<String>> supers,
                                        Set<String> declared,
                                        Map<String, Set<String>> implementers) {
        Set<String> found = new HashSet<>();
        found.add(callee);
        String owner = callee.substring(0, callee.indexOf('#'));
        String member = callee.substring(callee.indexOf('#'));
        if (owner.startsWith("java/")) {
            return found;
        }
        String declaring = callee;
        if (!declared.contains(callee)) {
            for (String above : supers.getOrDefault(owner, Set.of())) {
                if (declared.contains(above + member)) {
                    declaring = above + member;
                    found.add(declaring);
                    break;
                }
            }
        }
        found.addAll(implementers.getOrDefault(declaring, Set.of()));
        found.addAll(implementers.getOrDefault(callee, Set.of()));
        return found;
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
        Set<String> declared = new HashSet<>();
        for (ClassModel each : classes) {
            String owner = each.thisClass().asInternalName();
            for (MethodModel method : each.methods()) {
                declared.add(AMethod.of(each, method));
                if (method.code().isPresent()) {
                    withCode.add(AMethod.of(each, method));
                }
                if (overridable(method)) {
                    String self = AMethod.of(each, method);
                    for (String above : supers.get(owner)) {
                        if (above.startsWith("java/")) {
                            continue;
                        }
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
        Set<String> handingBack = new HashSet<>();
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
                                    .equals(ModelVocabulary.DB) && !makesAModelOfItsOwn(each,
                                    method);
                            if (fromOutside && owner.equals(ModelVocabulary.DB)
                                    && ModelVocabulary.DB_CHANGES.contains(name)) {
                                changing.add(self);
                            }
                            if (fromOutside && owner.equals(ModelVocabulary.DB)
                                    && ModelVocabulary.DB_READS_A_REPORT.contains(name)) {
                                reading.add(self);
                            }
                            String callee = AMethod.of(owner, name, call.type().stringValue());
                            for (String target : resolved(callee, supers, declared,
                                    implementers)) {
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
                    if (ModelVocabulary.SAYS_WITHOUT_REPORTS
                            .contains(method.methodName().stringValue())) {
                        reading.add(AMethod.of(each, method));
                    }
                    if (carriesReports(method)) {
                        handingBack.add(AMethod.of(each, method));
                    }
                }
            }
        }
        Set<String> readers = close(reading, calledBy);
        readers.addAll(handingBack);
        return new ModelEffects(implementers, supers, declared, withCode,
                close(changing, calledBy), readers);
    }

    /**
     * Whether the method is of a model's own making: a constructor or a factory of the class, which
     * work on the model they make and not on one that exists.
     */
    private static boolean makesAModelOfItsOwn(ClassModel each, MethodModel method) {
        return each.thisClass().asInternalName().equals(ModelVocabulary.COMPILATION)
                && (method.flags().has(AccessFlag.STATIC)
                || method.methodName().stringValue().startsWith("<"));
    }

    /**
     * Whether what the method hands back is made of what a model found, which is said by the types
     * it names: the reports, the errors and the places they are told at, and the failure they
     * make.
     */
    private static boolean carriesReports(MethodModel method) {
        String generic = method.findAttribute(Attributes.signature())
                .map(found -> found.signature().stringValue()).orElse("");
        String said = method.methodTypeSymbol().returnType().descriptorString()
                + generic.substring(generic.lastIndexOf(')') + 1);
        String taken = method.methodType().stringValue().substring(0,
                method.methodType().stringValue().lastIndexOf(')'))
                + generic.substring(0, Math.max(0, generic.lastIndexOf(')')));
        return ModelVocabulary.REPORT_CARRIERS.stream().anyMatch(said::contains)
                && ModelVocabulary.REPORT_CARRIERS.stream().noneMatch(taken::contains);
    }

    /** The methods the call of {@code callee} may run: see {@link #resolved}. */
    Set<String> targets(String callee) {
        return resolved(callee, supers, declared, implementers);
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
