package souther.architecture;

import souther.test.Nightly;
import souther.test.RepositoryLayout;

import org.junit.jupiter.api.Test;

import java.lang.classfile.Annotation;
import java.lang.classfile.Attributes;
import java.lang.classfile.ClassModel;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * What is deferred to the nightly is a whole file of tests.
 *
 * <p>{@link Nightly} is written at a type, which is where JUnit reads a tag from, and a tag at a
 * class covers the {@code @Nested} classes in it. So the annotation would also be legal inside one,
 * deferring part of a file and leaving the rest in the run a change waits on.
 *
 * <p><b>And the readers of it do not agree about that.</b> What surefire leaves out is the nested
 * class; {@code bin/CoverageSubsumption} folds every nested class into the outermost one, because
 * one file of test source is one class to it, and asks which classes a pull request's run leaves
 * out so that it can say whose coverage stands alone in that run. A file deferred in part is a file
 * the two read differently, and neither of them would say so — which is the kind of drift the
 * annotation exists to stop, reappearing under it.
 *
 * <p>So the annotation goes at the top of a file or nowhere, and the two readings are the same
 * reading. A nested class too slow to wait on is a file of its own, which is also what says so to
 * whoever opens it.
 */
class WhatIsDeferredToTheNightlyIsAWholeTestClassTest {

    private static final RepositoryLayout REPOSITORY = RepositoryLayout.ofWorkingDirectory();

    private static final CompiledOutputs TESTS = CompiledOutputs.ofEverythingCompiledHere();

    /** How the annotation is written in a class file. */
    private static final String DEFERRED = "L" + Nightly.class.getName().replace('.', '/') + ";";

    @Test
    void nothingNestedCarriesIt() {
        TreeSet<String> nested = new TreeSet<>();
        int whole = 0;
        for (Path module : REPOSITORY.modules()) {
            for (ClassModel each : TESTS.testClassesOf(module)) {
                String name = each.thisClass().asInternalName();
                if (!Files.isRegularFile(sourceOf(module, name)) || !defers(each)) {
                    continue;
                }
                if (name.contains("$")) {
                    nested.add(name.replace('/', '.'));
                } else {
                    whole++;
                }
            }
        }

        // And something carries it where it belongs, which is what says this walked the annotations
        // rather than a set of class files none of them is in.
        assertFalse(whole == 0,
                "no test class is deferred to the nightly at all, so this holds by finding nothing"
                        + " rather than by finding it in the right place");

        assertEquals(List.of(), List.copyOf(nested),
                "@" + Nightly.class.getSimpleName() + " written inside a test class: surefire would"
                        + " leave out the nested class and the coverage reader would read the whole"
                        + " file as deferred. It goes at the top of a file, or the cases it is"
                        + " about become one");
    }

    /** Where the source of one compiled test would be, its nesting read off the name. A class file
     *  with no source is what a previous build left, and is passed over. */
    private static Path sourceOf(Path module, String internalName) {
        String outer = internalName.contains("$")
                ? internalName.substring(0, internalName.indexOf('$')) : internalName;
        return module.resolve("src").resolve("test").resolve("java").resolve(outer + ".java");
    }

    private static boolean defers(ClassModel model) {
        return model.findAttribute(Attributes.runtimeVisibleAnnotations())
                .stream()
                .flatMap(annotations -> annotations.annotations().stream())
                .map(Annotation::className)
                .anyMatch(name -> DEFERRED.equals(name.stringValue()));
    }
}
