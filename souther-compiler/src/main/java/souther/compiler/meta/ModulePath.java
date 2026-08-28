package souther.compiler.meta;

import souther.compiler.jvm.ClassFileImage;
import souther.compiler.jvm.JvmClassName;
import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.Map;
import java.util.zip.ZipEntry;
import java.util.zip.ZipFile;

/**
 * Where already-compiled modules are found: the class files of the projects this one depends on.
 *
 * <p>One input serves both things a compile needs from a dependency. Its declarations are read out
 * of the same class files that {@link #loader} hands to the constant evaluation and the example
 * runs — so what an import resolves against and what an example actually calls cannot be two
 * different versions of the module.
 */
public interface ModulePath {

    /** Nothing is on the path: every module has to be among the sources being compiled. */
    ModulePath EMPTY = _ -> null;

    /** The class file of {@code binaryName}, or null when this path has none. */
    byte[] bytes(String binaryName);

    /** The declarations published on these classes. */
    default PublishedClasses declarations() {
        return new ClassFileDeclarations(this::bytes);
    }

    /** A loader over these classes, under {@code parent}. The compile's own generated classes go on
     * top of this, and what makes a module being compiled win over one of the same name here is that
     * {@link souther.compiler.generated.MemoryClassLoader} looks in itself first for the names it holds — a
     * loader that delegated first would answer with these, whatever was put on top. */
    default ClassLoader loader(ClassLoader parent) {
        return new ClassLoader(parent) {
            @Override
            protected Class<?> findClass(String name) throws ClassNotFoundException {
                byte[] bytes = ModulePath.this.bytes(name);
                if (bytes == null) {
                    throw new ClassNotFoundException(name);
                }
                return defineClass(name, bytes, 0, bytes.length);
            }
        };
    }

    /** The classes on an ordinary class path: directories and jars, read in order. Nothing is held
     * open between reads, so a path can be built as often as a compile is run. */
    static ModulePath ofClassPath(List<Path> entries) {
        return new ClassPath(List.copyOf(entries));
    }

    /**
     * A path over class files already in hand — what another compile came to, without writing them
     * anywhere.
     *
     * <p>Here rather than at each caller for the reason {@link ClassPath} is a record: two paths
     * over the same classes are the same path, and a caller writing the lookup itself hands over
     * something that is a new path every time it is built.
     */
    static ModulePath of(Map<String, ClassFileImage> classes) {
        return new Held(classes);
    }

    /** A path over class files in hand, by the binary name each is under. */
    record Held(Map<String, ClassFileImage> classes) implements ModulePath {

        public Held {
            classes = Map.copyOf(classes);
        }

        @Override
        public byte[] bytes(String binaryName) {
            ClassFileImage image = classes.get(binaryName);
            return image == null ? null : image.bytes();
        }
    }

    /**
     * A class path, by its entries. It is a value rather than a lambda so that two paths over the
     * same entries are the same path: a language server rebuilds one on every request, and a
     * compilation it wants to keep between edits has to be able to tell that nothing moved.
     */
    record ClassPath(List<Path> entries) implements ModulePath {
        @Override
        public byte[] bytes(String binaryName) {
            String resource = JvmClassName.classFile(binaryName);
            for (Path entry : entries) {
                byte[] bytes = read(entry, resource);
                if (bytes != null) {
                    return bytes;
                }
            }
            return null;
        }
    }

    /** One class path entry's copy of {@code resource}, or null when it has none. An entry that is
     * not there at all reads as having none, the same as one that is there without the class. */
    private static byte[] read(Path entry, String resource) {
        try {
            if (Files.isDirectory(entry)) {
                Path file = entry.resolve(resource);
                return Files.isRegularFile(file) ? Files.readAllBytes(file) : null;
            }
            if (!Files.isRegularFile(entry)) {
                return null;
            }
            try (ZipFile jar = new ZipFile(entry.toFile())) {
                ZipEntry found = jar.getEntry(resource);
                if (found == null) {
                    return null;
                }
                try (InputStream in = jar.getInputStream(found)) {
                    return in.readAllBytes();
                }
            }
        } catch (IOException e) {
            throw new IllegalStateException("cannot read " + resource + " from " + entry, e);
        }
    }
}
