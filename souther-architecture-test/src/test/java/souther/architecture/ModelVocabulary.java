package souther.architecture;

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

    /** What changes what a model is compiled from, through the store it hands out. */
    static final Set<String> DB_CHANGES = Set.of("running", "allowing", "set", "forget",
            "abandonWhen");

    /** What asks a store what it holds, or what it was asked, and changes nothing. */
    static final Set<String> DB_NEITHER = Set.of("readings", "execution", "allowances", "ask",
            "dependenciesOf", "isComputed", "watching", "everyAnswer", "revision",
            "ruleReadingFor");

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
