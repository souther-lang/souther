package souther.architecture;

import souther.test.CheckedInObservation;
import souther.test.ClosedWorldContract;
import souther.test.RepositoryLayout;

import org.junit.jupiter.api.Test;

import java.lang.classfile.Annotation;
import java.lang.classfile.Attributes;
import java.lang.classfile.ClassModel;
import java.lang.classfile.constantpool.ClassEntry;
import java.lang.classfile.constantpool.PoolEntry;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every test that sweeps a corpus says what it claims of one.
 *
 * <p>A test reaching the models this repository carries is asking about the language rather than
 * about a source somebody wrote to ask one question, and there is more than one thing such a test
 * can be. It can close a set the compiler declares and hold that nothing is missing from it, or it
 * can hold what the compiler answers against an answer written down here. Which of those it is
 * decides what a reader does with a red one, and nothing about the code says it.
 *
 * <p><b>So the claim is declared and is not worked out here.</b> Reaching a corpus is a fact about
 * the constant pool and is read off it; what the test claims is a fact about the sentence at the top
 * of the file, and a rule that guessed it from the reach would be putting words in the author's
 * mouth — which is what a table of exceptions beside such a rule is for, and why there was one.
 * Asked for instead: a test that reaches a corpus and says nothing fails here, and the author writes
 * the one word that settles it.
 *
 * <p><b>And it says nothing about when the test runs.</b> {@link souther.test.Nightly} is the other
 * annotation and is free of this one: a contract too slow to wait on carries both, and a test whose
 * claim this is about carries this one whether or not a plain run asks it. Neither is derived from
 * the other, because what a test establishes is stable and what it is worth paying for is not.
 *
 * <p>The corpora are named below rather than recognised. A corpus is a thing somebody wrote to be
 * swept, and there are few of them; a rule that guessed which classes were corpora would be a second
 * account of the same short list, and the two would disagree the first time one moved.
 *
 * <p><b>What this sees is a test that reaches one of the corpora named below.</b> A test that walks
 * this repository's own sources or its specification some other way — through
 * {@link RepositoryLayout} and a suffix, say — sweeps a population too and is not one of these, so
 * it is asked for nothing here. Naming the layout as a corpus would not close it either: reading
 * class files to answer a question about this compiler goes through the same door, and every check
 * in this package would come back as one of these.
 */
class EveryTestThatSweepsACorpusSaysWhatItClaimsTest {

    private static final RepositoryLayout REPOSITORY = RepositoryLayout.ofWorkingDirectory();

    private static final CompiledOutputs TESTS = CompiledOutputs.ofEverythingCompiledHere();

    /**
     * The annotations one of these says its claim with, as class-file descriptors.
     *
     * <p>Exactly one, and the alternatives are here rather than in the assertion so that the two
     * ways of being wrong — none of them, and more than one — are one question asked once. A test
     * carrying both would be claiming to record an answer and to close a set, which are different
     * things to do about a red run.
     */
    private static final Map<String, Class<?>> CLAIMS = Map.of(
            "L" + ClosedWorldContract.class.getName().replace('.', '/') + ";",
            ClosedWorldContract.class,
            "L" + CheckedInObservation.class.getName().replace('.', '/') + ";",
            CheckedInObservation.class);

    /**
     * What hands out a population, as binary names.
     *
     * <p>Each reads something the repository carries and hands it out to be swept: the conformance
     * corpora and the models compiled beside them, and the sources the formatter is held to. A test
     * that reaches one of these is asking about all of what it hands out.
     */
    private static final Set<String> CORPORA = Set.of(
            "souther/compiler/conformance/ConformanceCorpus",
            "souther/compiler/conformance/RepositoryModels",
            "souther/compiler/fmt/FormatterCorpus",
            "souther/compiler/fmt/WhatGoesBetweenTwoTokensOnALineTest",
            "souther/bench/Corpus");

    @Test
    void everyTestReachingACorpusDeclaresWhatItClaims() {
        Map<String, Set<String>> references = referencesByClass();
        assertFalse(references.isEmpty(),
                "no compiled test was read, so this walked nothing and would hold either way");

        TreeSet<String> silent = new TreeSet<>();
        TreeSet<String> saidTwice = new TreeSet<>();
        for (String each : reachingACorpus(references)) {
            if (!each.endsWith("Test")) {
                // A helper a test reaches through. It runs nothing of its own, so nothing about it
                // is a claim somebody would act on.
                continue;
            }
            int said = claims(each).size();
            if (said == 0) {
                silent.add(each.replace('/', '.'));
            } else if (said > 1) {
                saidTwice.add(each.replace('/', '.'));
            }
        }

        assertEquals(List.of(), List.copyOf(saidTwice),
                "a test sweeping a corpus under more than one of " + CLAIMS.values() + ": what a"
                        + " reader does with a red run is one of those things and not both");

        assertEquals(List.of(), List.copyOf(silent),
                "a test whose subjects come from this repository, saying nothing about what it"
                        + " claims of them: it carries one of " + CLAIMS.values() + " or it stops"
                        + " reaching a corpus");
    }

    /**
     * And something reaches one, which is what says the walk read the pools rather than empty files.
     *
     * <p>Without it a walk that parsed nothing, or one whose corpora had all been renamed, would pass
     * the check above by finding no test to hold to it.
     */
    @Test
    void andSomeTestDoesReachACorpus() {
        Set<String> reaching = reachingACorpus(referencesByClass());
        assertTrue(reaching.stream().anyMatch(each -> each.endsWith("Test")),
                "no test reaches any of " + CORPORA + ", so the names above are stale and this holds"
                        + " for a reason other than the one it states");
    }

    /**
     * The compiled tests this walk is over, by binary name.
     *
     * <p><b>Only the ones a source still writes.</b> Nothing here removes a class file, and the
     * build is not run with {@code clean}, so a test renamed or deleted leaves its old one behind.
     * Read as a test, it would be held to an annotation its author cannot add to a source that no
     * longer exists — and if the rename is what added the annotation, the check would name a class
     * nobody can find. A class file with no source is what a previous build left, and is passed
     * over.
     *
     * <p><b>And a name can be more than one class.</b> Packages are written under more than one
     * module here — {@code souther.compiler.inputs} holds a fixtures class in two of them — so a
     * name does not settle which class file it is. Kept as one, the second would replace the first
     * and whichever lost would be neither held to the rule nor read for an answer to it. All of them
     * are kept instead, and what a name reaches or claims is what any of them does: which one a
     * reference meant is what this cannot say, and asking for a claim where either would want one is
     * the side of that to be wrong on.
     */
    private static Map<String, List<ClassModel>> compiled;

    private static Map<String, List<ClassModel>> compiledTests() {
        if (compiled != null) {
            return compiled;
        }
        Map<String, List<ClassModel>> out = new LinkedHashMap<>();
        for (Path module : REPOSITORY.modules()) {
            for (ClassModel each : TESTS.testClassesOf(module)) {
                String name = each.thisClass().asInternalName();
                if (!Files.isRegularFile(sourceOf(module, name))) {
                    continue;
                }
                out.computeIfAbsent(name, one -> new ArrayList<>()).add(each);
            }
        }
        compiled = out;
        return out;
    }

    /** Where the source of one compiled test would be, its nesting read off the name. */
    private static Path sourceOf(Path module, String internalName) {
        String outer = internalName.contains("$")
                ? internalName.substring(0, internalName.indexOf('$')) : internalName;
        return module.resolve("src").resolve("test").resolve("java").resolve(outer + ".java");
    }

    /** Every compiled test, with the classes each names in its constant pool. */
    private static Map<String, Set<String>> referencesByClass() {
        Map<String, Set<String>> out = new LinkedHashMap<>();
        compiledTests().forEach((name, every) -> {
            Set<String> named = new LinkedHashSet<>();
            for (ClassModel each : every) {
                for (PoolEntry entry : each.constantPool()) {
                    if (entry instanceof ClassEntry it) {
                        named.add(it.asInternalName());
                    }
                }
            }
            out.put(name, named);
        });
        return out;
    }

    /** The classes that name a corpus, and the classes that reach one through them. */
    private static Set<String> reachingACorpus(Map<String, Set<String>> references) {
        Set<String> reaching = new LinkedHashSet<>();
        Deque<String> pending = new ArrayDeque<>(CORPORA);
        while (!pending.isEmpty()) {
            String target = pending.removeFirst();
            for (Map.Entry<String, Set<String>> each : references.entrySet()) {
                if (each.getValue().contains(target) && reaching.add(each.getKey())) {
                    pending.addLast(each.getKey());
                }
            }
        }
        // A corpus that is itself a test class reaches itself and is one of these.
        CORPORA.stream().filter(references::containsKey).forEach(reaching::add);
        return reaching;
    }

    /**
     * The claims one compiled test is written under, which are its own and the ones it is written
     * inside.
     *
     * <p>A claim made at a class covers the {@code @Nested} classes in it — one file of test source
     * is one sentence, and the author writes it once at the top. Read off the class alone, a nested
     * test inside a declared one comes back silent here and the author is told to say again what the
     * file already says.
     */
    private static Set<Class<?>> claims(String internalName) {
        Map<String, List<ClassModel>> tests = compiledTests();
        Set<Class<?>> out = new LinkedHashSet<>();
        for (String each = internalName; each != null; each = enclosing(each)) {
            for (ClassModel where : tests.getOrDefault(each, List.of())) {
                out.addAll(claimsOf(where));
            }
        }
        return out;
    }

    /** The class one is written inside, or null where it is written at the top of its file. */
    private static String enclosing(String internalName) {
        int nested = internalName.lastIndexOf('$');
        return nested < 0 ? null : internalName.substring(0, nested);
    }

    private static Set<Class<?>> claimsOf(ClassModel model) {
        Set<Class<?>> out = new LinkedHashSet<>();
        model.findAttribute(Attributes.runtimeVisibleAnnotations()).ifPresent(annotations -> {
            for (Annotation each : annotations.annotations()) {
                Class<?> claim = CLAIMS.get(each.className().stringValue());
                if (claim != null) {
                    out.add(claim);
                }
            }
        });
        return out;
    }
}
