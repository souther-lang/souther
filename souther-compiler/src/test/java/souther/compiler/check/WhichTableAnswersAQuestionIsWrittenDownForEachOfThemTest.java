package souther.compiler.check;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.lang.classfile.ClassFile;
import java.lang.classfile.ClassModel;
import java.lang.classfile.MethodModel;
import java.lang.classfile.constantpool.FieldRefEntry;
import java.lang.classfile.instruction.FieldInstruction;
import java.io.File;
import java.lang.reflect.AccessFlag;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every question the derived world answers says which of its tables answers it.
 *
 * <p>The world holds three, and each answers what it settled: the derived declarations say what a
 * representation was derived for, the normalized ones say what a declaration is read as, and the
 * resolution says which names are declared and what a spelling means. Only the first is short of the
 * declarations a module writes, so it is the only one whose emptiness means anything — and a
 * question answered from it is a question whose answer turns on whether a representation could be
 * derived.
 *
 * <p>Which is a thing to decide per question and not to notice afterwards. {@code scope()} was
 * answered from the derived table for no reason but that the table had one, and a name written out
 * in full then denoted nothing where no representation had been derived
 * ({@code WhatANameMeansIsNotDecidedByWhatWasDerivedForItTest}). The list below is what the answer
 * is today; a member added or moved changes it, and the reason goes here with the change.
 *
 * <p>Read off the class file rather than off the source, because what is asked is which field the
 * method reads and a body that delegates through another method would read as neither.
 */
class WhichTableAnswersAQuestionIsWrittenDownForEachOfThemTest {

    /**
     * The questions the partial table answers.
     *
     * <p>Every one of them is about the representation itself, which is what that table holds. A
     * question about a declaration or about a name is not here, and one that arrives here has to say
     * why its answer may turn on a derivation.
     */
    private static final Set<String> FROM_THE_DERIVED_TABLE = new LinkedHashSet<>(List.of(
            "declarations", "reachable", "derived"));

    @Test
    void onlyTheQuestionsAboutARepresentationAreAnsweredFromTheDerivedTable() {
        assertEquals(FROM_THE_DERIVED_TABLE, reading("table"),
                "a question answered from the derived table is one whose answer turns on whether a"
                        + " representation could be derived for the declaration it is about");
    }

    /** And the reading of a declaration is the normalized table's, which is short of nothing. */
    @Test
    void aDeclarationIsReadFromTheNormalizedTable() {
        assertEquals(Set.of("declaredNode"), reading("normalized"));
    }

    /** Everything else is resolution's: which names are declared, what a spelling means, and what
     *  this is a scope of. */
    @Test
    void whatIsLeftIsAnsweredFromTheResolution() {
        Set<String> fromResolution = reading("resolved");

        assertTrue(fromResolution.containsAll(List.of("scope", "declares", "declaredByCompilation",
                        "declaredNamesIn", "module", "library")),
                "answered from the resolution: " + fromResolution);
        assertEquals(Set.of("reachable"), intersection(fromResolution, FROM_THE_DERIVED_TABLE),
                "the one question that is two: which spellings are in scope is resolution's, and"
                        + " what the derived table holds under each of them is the table's. A"
                        + " second question reading two tables is one whose answer moves with"
                        + " whichever came back first");
    }

    /** The methods of {@link DerivedSymbols} that read {@code field}. */
    private static Set<String> reading(String field) {
        Set<String> found = new LinkedHashSet<>();
        for (MethodModel method : model().methods()) {
            if (method.methodName().stringValue().equals("<init>")
                    || method.methodName().stringValue().equals("over")) {
                continue;   // building the tables is not answering a question from one
            }
            method.code().ifPresent(code -> code.elementList().forEach(each -> {
                if (each instanceof FieldInstruction read
                        && read.field() instanceof FieldRefEntry ref
                        && ref.name().stringValue().equals(field)) {
                    found.add(method.methodName().stringValue());
                }
            }));
        }
        return found;
    }

    private static Set<String> intersection(Set<String> one, Set<String> other) {
        Set<String> both = new LinkedHashSet<>(one);
        both.retainAll(other);
        return both;
    }

    private static ClassModel model() {
        for (String entry : System.getProperty("java.class.path").split(File.pathSeparator)) {
            Path candidate = Path.of(entry)
                    .resolve("souther/compiler/check/DerivedSymbols.class");
            if (Files.isRegularFile(candidate)) {
                try {
                    return ClassFile.of().parse(Files.readAllBytes(candidate));
                } catch (IOException e) {
                    throw new UncheckedIOException(e);
                }
            }
        }
        throw new AssertionError("the class this rule is about was not on the path");
    }

    /**
     * And every question is answered by reading a table, not by asking another question here.
     *
     * <p>What the readings above count is the field a method reads. A method that answered by
     * calling one of its neighbours would read no table at all and would be in none of the three
     * sets — so the rule would be silent about it, while the neighbour it called decides its answer.
     * Held instead of following the call: which table answers a question is a thing to say at the
     * question, and a method that says it by delegating has not said it.
     */
    @Test
    void everyQuestionReadsATableItself() {
        Set<String> answered = new LinkedHashSet<>();
        answered.addAll(reading("table"));
        answered.addAll(reading("normalized"));
        answered.addAll(reading("resolved"));

        List<String> silent = new ArrayList<>();
        for (MethodModel method : model().methods()) {
            String name = method.methodName().stringValue();
            // A synthetic method is not a question this class answers: what the compiler wrote for
            // a lambda belongs to the method that wrote it, and building the tables is not
            // answering from one.
            if (method.flags().has(AccessFlag.SYNTHETIC)
                    || name.equals("<init>") || name.equals("over") || answered.contains(name)) {
                continue;
            }
            silent.add(name);
        }

        assertEquals(List.of(), silent,
                "a question here reads one of the three tables, or it is answered by whichever"
                        + " question it delegated to and this rule says nothing about it");
    }

    /** Held so the reading above is over the members this file writes and not over a class it could
     *  not find: a scan of nothing reports nothing read from anywhere. */
    @Test
    void theScanReachesTheMembersThisRuleIsAbout() {
        List<String> answering = new ArrayList<>();
        for (MethodModel method : model().methods()) {
            answering.add(method.methodName().stringValue());
        }

        assertTrue(answering.contains("scope") && answering.contains("declaredNode")
                        && answering.contains("derived"),
                "the members this rule is about were not found: " + answering);
    }
}
