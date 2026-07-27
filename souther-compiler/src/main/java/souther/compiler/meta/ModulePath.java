package souther.compiler.meta;

import java.io.IOException;
import java.io.InputStream;
import java.net.MalformedURLException;
import java.net.URL;
import java.net.URLClassLoader;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

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

    /** The classes on an ordinary class path: directories and jars, read in order. */
    static ModulePath ofClassPath(List<Path> entries) {
        List<URL> urls = new ArrayList<>();
        for (Path entry : entries) {
            try {
                urls.add(entry.toUri().toURL());
            } catch (MalformedURLException e) {
                throw new IllegalArgumentException("not a readable class path entry: " + entry, e);
            }
        }
        URLClassLoader reader = new URLClassLoader(urls.toArray(new URL[0]), null);
        return binaryName -> {
            String resource = binaryName.replace('.', '/') + ".class";
            try (InputStream in = reader.getResourceAsStream(resource)) {
                return in == null ? null : in.readAllBytes();
            } catch (IOException e) {
                throw new IllegalStateException("cannot read " + resource, e);
            }
        };
    }
}
