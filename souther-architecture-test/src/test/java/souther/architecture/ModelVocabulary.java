package souther.architecture;

import java.lang.classfile.ClassModel;
import java.lang.classfile.MethodModel;
import java.lang.reflect.AccessFlag;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

/**
 * What the check allows to be done to a model and to the store it hands out, said once.
 *
 * <p>A check that proves of any code that a read of a model is of one that was asked about has to
 * follow every way the code can reach the model, and what it does not follow it lets through. So it
 * proves it of a closed set of things done, and refuses the rest. What can be done to a model is
 * what its class has, and what its store has, and each of those methods is here, said to read what
 * the model says, to change what the model is, or to do neither. A method added to either class and
 * said here nowhere is found by {@link #unsaid}, which a test holds empty, so that a change to
 * what a model can do is a change that says which of the three it is.
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
     * What a test calls on a model to read what is said of it. What these say of a model that did
     * not compile is nothing, which is also what they say of one with nothing to say.
     */
    static final Set<String> COMPILATION_READS = Set.of("db", "adequacy", "warnings");

    /**
     * What changes a model once it has been asked about, so that what was asked is no longer what
     * it is: the sources it is made of, and the way it is compiled and measured.
     */
    static final Set<String> COMPILATION_CHANGES = Set.of("update", "measure", "observe",
            "abandonWhen", "allowing", "withExampleBudget", "withJvmExampleDeadlines",
            "withEvaluationPolicy", "writtenOn", "withReadingPolicy", "withAdequacyPolicy");

    /**
     * What neither reads what is said of a model nor changes it: what it is made of, what answering
     * it has made, and the errors, which a model that did not compile does say.
     */
    static final Set<String> COMPILATION_NEITHER = Set.of("jvmProgramImages", "classes", "loader",
            "module", "declaredBehaviors", "signatures", "sourceIds", "answerEverything",
            "answerWarnings", "exampleSourcesOf", "texts", "modules", "sourceIdOf", "moduleOf",
            "structuralReports", "diagnostics", "repairs", "reports", "failure",
            "structuralFailure", "filedUnderOf", "publishSourceIdsOf", "errors");

    /** What reads of a model's store what its reports say. */
    static final Set<String> DB_READS_A_REPORT = Set.of("allReports");

    /** What changes what a model is compiled from, through the store it hands out. */
    static final Set<String> DB_CHANGES = Set.of("running", "allowing", "set", "forget",
            "abandonWhen");

    /** What asks a store what it holds, or what it was asked, and changes nothing. */
    static final Set<String> DB_NEITHER = Set.of("readings", "execution", "allowances", "ask",
            "dependenciesOf", "isComputed", "watching", "everyAnswer", "revision",
            "ruleReadingFor");

    /**
     * The methods of the two classes that are said nowhere above, as {@code Class#name}, which are
     * the instance methods a caller outside can reach.
     */
    static Set<String> unsaid(ClassModel compilation, ClassModel db) {
        Set<String> unsaid = new TreeSet<>();
        unsaid.addAll(unsaidOf(compilation, List.of(COMPILATION_READS, COMPILATION_CHANGES,
                COMPILATION_NEITHER)));
        unsaid.addAll(unsaidOf(db, List.of(DB_READS_A_REPORT, DB_CHANGES, DB_NEITHER)));
        return unsaid;
    }

    private static Set<String> unsaidOf(ClassModel model, List<Set<String>> said) {
        Set<String> unsaid = new TreeSet<>();
        for (MethodModel method : model.methods()) {
            String name = method.methodName().stringValue();
            boolean reachable = !method.flags().has(AccessFlag.STATIC)
                    && !method.flags().has(AccessFlag.PRIVATE)
                    && !method.flags().has(AccessFlag.SYNTHETIC)
                    && !name.startsWith("<") && !name.startsWith("lambda$");
            if (reachable && said.stream().noneMatch(each -> each.contains(name))) {
                unsaid.add(model.thisClass().asInternalName() + "#" + name);
            }
        }
        return unsaid;
    }
}
