package souther.architecture;

import souther.test.RepositoryLayout;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.lang.classfile.ClassFile;
import java.lang.classfile.ClassModel;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.HashMap;
import java.util.Map;
import java.util.Optional;

/**
 * The class files this repository built, found through the repository.
 *
 * <p>Not through {@code java.class.path}. What a module is handed there is the reactor's to decide
 * and it is not the same in every build — a module built beside this one arrives as its
 * {@code target/classes}, and one already packaged arrives as a jar — so a walk over the entries is
 * a walk over something that answers differently depending on which goal was run. What a rule here
 * is about is the compiled surface of a class of this repository, and the repository is where that
 * is.
 *
 * <p>Test output is searched beside main output, because the subjects a reading's own test declares
 * to be read are compiled there.
 *
 * <p>A name this cannot find is not a class that reaches nothing. It is a question this cannot
 * answer, and it says so rather than answering.
 */
final class CompiledClasses {

    private final RepositoryLayout repository;

    private final Map<String, Optional<ClassModel>> read = new HashMap<>();

    private CompiledClasses(RepositoryLayout repository) {
        this.repository = repository;
    }

    static CompiledClasses ofRepository() {
        return new CompiledClasses(RepositoryLayout.ofWorkingDirectory());
    }

    /** The class {@code internalName} names, or nothing where this repository built no such file. */
    Optional<ClassModel> find(String internalName) {
        return read.computeIfAbsent(internalName, this::parse);
    }

    /** The class {@code internalName} names, where failing to find one fails the reading. */
    ClassModel read(String internalName) {
        return find(internalName).orElseThrow(() -> new AssertionError(
                "the class " + internalName.replace('/', '.') + " was not built here, so what a"
                        + " signature naming it reaches is a question this cannot answer"));
    }

    private Optional<ClassModel> parse(String internalName) {
        for (Path module : repository.modules()) {
            Path target = module.resolve("target");
            for (String output : new String[] {"classes", "test-classes"}) {
                Path compiled = target.resolve(output).resolve(internalName + ".class");
                if (Files.isRegularFile(compiled)) {
                    try {
                        return Optional.of(ClassFile.of().parse(Files.readAllBytes(compiled)));
                    } catch (IOException e) {
                        throw new UncheckedIOException(e);
                    }
                }
            }
        }
        return Optional.empty();
    }
}
