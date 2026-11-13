package souther.architecture;

import java.lang.classfile.Attributes;
import java.lang.classfile.ClassModel;
import java.lang.classfile.MethodModel;
import java.lang.reflect.AccessFlag;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

/**
 * What is said by hand of a model's store, and the names the check needs of the classes around it.
 *
 * <p>A check that proves of any code that a read of a model is of one that was asked about has to
 * follow every way the code can reach the model, and what it does not follow it lets through. What
 * a method of {@code Compilation} does is not said here: whether it reads a report or changes what
 * the model is made of is worked out from the classes ({@link ModelEffects}) by what it can reach
 * of the store, so it is right the day a method is added or its body is changed. What is said here
 * is the store's own operations, which are what the rest is worked out from, and
 * {@link #unsaid} finds a method of the store that is said nowhere, which a test holds empty.
 */
final class ModelVocabulary {

    private ModelVocabulary() { }

    static final String COMPILATION = "souther/compiler/query/Compilation";

    static final String COMPILATION_TYPE = "L" + COMPILATION + ";";

    static final String DB = "souther/compiler/query/Db";

    static final String DB_TYPE = "L" + DB + ";";

    static final String REPORT = "souther/compiler/report/AdequacyReport";

    /** The helper's way of saying a model is read without being compiled. */
    static final String NOT_COMPILED = "notCompiled";

    /**
     * The calls of the helper, and of what it keeps, that hand a model back and stop unless it is as
     * the test said. A model one of them hands back was asked about. What each does is held by
     * {@code ACompiledModelHoldsAModelToCompilingTest}, and a call of the helper that hands a model
     * back and is not here, or is {@link #NOT_COMPILED}, is found by {@link #unsaidChecks}.
     */
    static final Set<String> CHECKS = Set.of("compiles", "refusedWith", "refusedOnlyWith",
            "answered", "measured");

    /**
     * The calls of the helper class, as {@code Class#name}, that hand a model back and are neither
     * a check nor the way of saying a model is not compiled.
     */
    static Set<String> unsaidChecks(ClassModel helper) {
        Set<String> unsaid = new TreeSet<>();
        for (MethodModel method : helper.methods()) {
            String name = method.methodName().stringValue();
            if (method.methodTypeSymbol().returnType().descriptorString().equals(COMPILATION_TYPE)
                    && method.flags().has(AccessFlag.PUBLIC) && !CHECKS.contains(name)
                    && !name.equals(NOT_COMPILED)) {
                unsaid.add(helper.thisClass().asInternalName() + "#" + name);
            }
        }
        return unsaid;
    }

    /**
     * The public methods of the class that hand a model back, as {@link AMethod} says them: the
     * class, the name and what it takes. A name alone is every overload at once, so what a check
     * is is said by what it takes, and a call that is added under the name of one is found.
     */
    static Set<String> signaturesHandingAModelBack(ClassModel helper) {
        Set<String> found = new TreeSet<>();
        for (MethodModel method : helper.methods()) {
            if (method.methodTypeSymbol().returnType().descriptorString().equals(COMPILATION_TYPE)
                    && method.flags().has(AccessFlag.PUBLIC)) {
                found.add(AMethod.of(helper, method));
            }
        }
        return found;
    }

    /** The names that more than one instance method of the class has. */
    static Set<String> overloadedNames(ClassModel model) {
        Set<String> once = new TreeSet<>();
        Set<String> overloaded = new TreeSet<>();
        for (MethodModel method : model.methods()) {
            String name = method.methodName().stringValue();
            if (!method.flags().has(AccessFlag.STATIC) && !method.flags().has(AccessFlag.PRIVATE)
                    && !method.flags().has(AccessFlag.SYNTHETIC) && !name.startsWith("<")
                    && !once.add(name)) {
                overloaded.add(name);
            }
        }
        return overloaded;
    }

    /** The checks that none of the classes has, as names. */
    static Set<String> checksMissing(List<ClassModel> helper) {
        Set<String> had = new TreeSet<>();
        for (ClassModel each : helper) {
            for (MethodModel method : each.methods()) {
                had.add(method.methodName().stringValue());
            }
        }
        Set<String> missing = new TreeSet<>(CHECKS);
        missing.removeAll(had);
        return missing;
    }

    /**
     * The report of a model that reads the measures it asks of the store itself, so it is not
     * reached from the store's reads of a report.
     */
    static final String ADEQUACY_REPORT_OF = "of";

    /**
     * What a method that hands back what a model found names in its types: the report and the
     * place it is told at, the errors, the offers to repair them, and the failure they make.
     */
    static final Set<String> REPORT_CARRIERS = Set.of("souther/compiler/query/Db$Found",
            "souther/compiler/diag/Located", "souther/compiler/diag/Diagnostic",
            "souther/compiler/diag/CompileException", "RepairOffer");

    /** The method of a model that hands out its store. */
    static final String STORE_ACCESSOR = "db";

    /**
     * What answers everything a model has to answer, so that the errors it has are found. A part of
     * it, such as the warnings of one module, is not this: it leaves the rest unanswered.
     */
    static final Set<String> ANSWERS = Set.of("answerEverything");

    /**
     * The methods of a model that hand back the errors and nothing else. A model that was answered
     * shows them whether or not it compiles, so they are read of it without it having been asked
     * that it compiles. Every other method that reads what a model found, the warnings and the
     * whole of the reports among them, can be read as saying nothing wrong of a model that has
     * errors, so it is read only of a model that was asked about.
     */
    static final Set<String> SHOWS_ERRORS = Set.of("errors", "failure");

    /**
     * What reads of a model what it says without going through the reports it found: how well the
     * rows cover it. A model that did not compile says nothing here, so it is read only of one
     * that was asked about.
     */
    static final Set<String> SAYS_WITHOUT_REPORTS = Set.of("adequacy");

    /** What reads of a store what its reports say. */
    static final Set<String> DB_READS_A_REPORT = Set.of("allReports");

    /**
     * What hands back answers, each of which holds the reports its question found. The reports of
     * the answer of one question put to the store are followed; the reports of an answer reached
     * through all of them are not, because they are read for the shape of what was answered and the
     * stores they are read of are of every origin.
     */
    static final Set<String> DB_HOLDS_ANSWERS = Set.of("ask", "everyAnswer");

    /** What changes what a model is compiled from, through the store it hands out. */
    static final Set<String> DB_CHANGES = Set.of("running", "allowing", "set", "forget",
            "abandonWhen");

    /** What asks a store what it holds, or what it was asked, and changes nothing. */
    static final Set<String> DB_NEITHER = Set.of("readings", "execution", "allowances", "ask",
            "dependenciesOf", "isComputed", "watching", "everyAnswer", "revision",
            "ruleReadingFor");

    /**
     * The static methods of a model that take a model or a store and are not changes: the rest of
     * the working out takes a static method of the class to work on the model it makes and not on
     * one that exists, which holds of them and is held here.
     */
    static final Set<String> STATIC_READS = Set.of("sourceIdOf");

    /** The type of what a question put to a store answers, which holds the reports it found. */
    static final String ANSWER = "souther/compiler/query/Answer";

    /**
     * The static methods of the class that take a model or a store as an argument, and are not said
     * to be reads, as {@code Class#name}.
     */
    static Set<String> unsaidStatics(ClassModel compilation) {
        Set<String> unsaid = new TreeSet<>();
        for (MethodModel method : compilation.methods()) {
            String taken = method.methodType().stringValue();
            taken = taken.substring(0, taken.lastIndexOf(')'));
            String name = method.methodName().stringValue();
            if (method.flags().has(AccessFlag.STATIC) && !method.flags().has(AccessFlag.PRIVATE)
                    && !method.flags().has(AccessFlag.SYNTHETIC) && !name.startsWith("<")
                    && (taken.contains(COMPILATION_TYPE) || taken.contains(DB_TYPE))
                    && !STATIC_READS.contains(name)) {
                unsaid.add(compilation.thisClass().asInternalName() + "#" + name);
            }
        }
        return unsaid;
    }

    /**
     * The methods of the store that hand back what holds reports, as names: the reports themselves
     * and the answer of a question, which holds the reports that question found.
     */
    static Set<String> handingBackReports(ClassModel db) {
        Set<String> found = new TreeSet<>();
        for (MethodModel method : db.methods()) {
            String returned = method.methodTypeSymbol().returnType().descriptorString();
            String generic = method.findAttribute(Attributes.signature())
                    .map(each -> each.signature().stringValue()).orElse("");
            String said = returned + generic.substring(generic.lastIndexOf(')') + 1);
            String name = method.methodName().stringValue();
            if (!method.flags().has(AccessFlag.STATIC) && !method.flags().has(AccessFlag.PRIVATE)
                    && !method.flags().has(AccessFlag.SYNTHETIC) && !name.startsWith("<")
                    && (said.contains(ANSWER) || REPORT_CARRIERS.stream()
                    .anyMatch(said::contains))) {
                found.add(name);
            }
        }
        return found;
    }

    /**
     * The methods of the store that are said nowhere above, as {@code Class#name}, which are the
     * instance methods a caller outside can reach.
     */
    static Set<String> unsaid(ClassModel db) {
        Set<String> unsaid = new TreeSet<>();
        List<Set<String>> said = List.of(DB_READS_A_REPORT, DB_CHANGES, DB_NEITHER);
        for (MethodModel method : db.methods()) {
            String name = method.methodName().stringValue();
            boolean reachable = !method.flags().has(AccessFlag.STATIC)
                    && !method.flags().has(AccessFlag.PRIVATE)
                    && !method.flags().has(AccessFlag.SYNTHETIC)
                    && !name.startsWith("<") && !name.startsWith("lambda$");
            if (reachable && said.stream().noneMatch(each -> each.contains(name))) {
                unsaid.add(db.thisClass().asInternalName() + "#" + name);
            }
        }
        return unsaid;
    }
}
