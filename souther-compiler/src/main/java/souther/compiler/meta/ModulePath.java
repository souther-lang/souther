package souther.compiler.meta;

import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
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
    default PublishedModule.Classes declarations() {
        return new ClassFileDeclarations(this::bytes);
    }

    /** A loader over these classes, under {@code parent}. The compile's own generated classes go on
     * top of this, so a module being compiled wins over one of the same name on the path. */
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
     * A class path, by its entries. It is a value rather than a lambda so that two paths over the
     * same entries are the same path: a language server rebuilds one on every request, and a
     * compilation it wants to keep between edits has to be able to tell that nothing moved.
     */
    record ClassPath(List<Path> entries) implements ModulePath {
        @Override
        public byte[] bytes(String binaryName) {
            String resource = binaryName.replace('.', '/') + ".class";
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
