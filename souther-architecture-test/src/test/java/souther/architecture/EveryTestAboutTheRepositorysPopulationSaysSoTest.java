package souther.architecture;

import souther.test.RepositoryLayout;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.lang.classfile.Annotation;
import java.lang.classfile.AnnotationValue;
import java.lang.classfile.Attributes;
import java.lang.classfile.ClassFile;
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
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every test whose subjects come from this repository says that it is one.
 *
 * <p>A test that sweeps the models this repository carries, or its sources, or its specification, is
 * asking about the language rather than about a source somebody wrote to ask one question. Answering
 * such a subject is most of what the suite costs, so a plain run leaves them out and the merge into
 * develop asks them. What decides which run a test lands in is the tag it carries.
 *
 * <p><b>So the tag cannot be a thing to remember.</b> A test reaching a corpus without one is left in
 * the run everybody waits on, and nothing about writing it would say so — the class compiles, passes,
 * and is slow somewhere else. The population is read off the compiled tests here instead: every test
 * class that reaches a corpus, by its own constant pool or through another test class that does.
 *
 * <p>The corpora are named below rather than recognised. A corpus is a thing somebody wrote to be
 * swept, and there are few of them; a rule that guessed which classes were corpora would be a second
 * account of the same short list, and the two would disagree the first time one moved.
 */
class EveryTestAboutTheRepositorysPopulationSaysSoTest {

    private static final RepositoryLayout REPOSITORY = RepositoryLayout.ofWorkingDirectory();

    /** What this tag is spelled as where a test carries it. */
    private static final String TAG = "population";

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
    void everyTestReachingACorpusCarriesTheTag() {
        Map<String, Set<String>> references = referencesByClass();
        assertFalse(references.isEmpty(),
                "no compiled test was read, so this walked nothing and would hold either way");

        Set<String> reaching = reachingACorpus(references);
        TreeSet<String> untagged = new TreeSet<>();
        for (String each : reaching) {
            if (!each.endsWith("Test")) {
                // A helper a test reaches through. It runs nothing of its own, so no tag decides
                // anything about it.
                continue;
            }
            if (!tags(each).contains(TAG)) {
                untagged.add(each.replace('/', '.'));
            }
        }

        assertEquals(List.of(), List.copyOf(untagged),
                "a test whose subjects come from this repository, in the run somebody waits on while"
                        + " editing: it carries @Tag(\"" + TAG + "\") or it stops reaching a corpus");
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

    /** Every compiled test, with the classes each names in its constant pool. */
    private static Map<String, Set<String>> referencesByClass() {
        Map<String, Set<String>> out = new LinkedHashMap<>();
        for (Path module : REPOSITORY.modules()) {
            Path where = testClassesOf(module);
            if (!Files.isDirectory(where)) {
                continue;
            }
            for (Path compiled : classesUnder(where)) {
                ClassModel model = parse(compiled);
                Set<String> named = new LinkedHashSet<>();
                for (PoolEntry entry : model.constantPool()) {
                    if (entry instanceof ClassEntry it) {
                        named.add(it.asInternalName());
                    }
                }
                out.put(model.thisClass().asInternalName(), named);
            }
        }
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

    /** The tags one compiled test carries, as they are written at the class. */
    private static Set<String> tags(String internalName) {
        for (Path module : REPOSITORY.modules()) {
            Path compiled = testClassesOf(module).resolve(internalName + ".class");
            if (Files.isRegularFile(compiled)) {
                return tagsOf(parse(compiled));
            }
        }
        return Set.of();
    }

    private static Set<String> tagsOf(ClassModel model) {
        Set<String> out = new LinkedHashSet<>();
        model.findAttribute(Attributes.runtimeVisibleAnnotations()).ifPresent(annotations -> {
            for (Annotation each : annotations.annotations()) {
                String type = each.className().stringValue();
                if (!"Lorg/junit/jupiter/api/Tag;".equals(type)) {
                    continue;
                }
                each.elements().stream()
                        .filter(element -> "value".equals(element.name().stringValue()))
                        .forEach(element -> {
                            if (element.value() instanceof AnnotationValue.OfString it) {
                                out.add(it.stringValue());
                            }
                        });
            }
        });
        return out;
    }

    private static ClassModel parse(Path compiled) {
        try {
            return ClassFile.of().parse(Files.readAllBytes(compiled));
        } catch (IOException e) {
            throw new UncheckedIOException("a compiled test is not readable: " + compiled, e);
        }
    }

    private static Path testClassesOf(Path module) {
        return module.resolve("target").resolve("test-classes");
    }

    private static List<Path> classesUnder(Path where) {
        try (Stream<Path> found = Files.walk(where)) {
            List<Path> out = new ArrayList<>();
            found.filter(each -> each.toString().endsWith(".class")).forEach(out::add);
            return out;
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }
}
