package souther.compiler.doc;

import javax.tools.FileObject;
import javax.tools.ForwardingJavaFileManager;
import javax.tools.JavaFileObject;
import javax.tools.SimpleJavaFileObject;
import javax.tools.StandardJavaFileManager;
import javax.tools.StandardLocation;
import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.net.URI;
import java.net.URISyntaxException;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;

/**
 * A file manager whose class path is a {@link ClassLookup} and nothing javac can open itself.
 *
 * <p>Every other location is the standard manager's. The class path is asked for by package and
 * kind only, so no directory is listed and no path is joined here: what a class path entry holds is
 * whatever the lookup says it holds, read the way the caller reads everything else. Sources are
 * never taken from the class path, which is where javac looks for them when it has no source path.
 */
final class ConfinedClassPath extends ForwardingJavaFileManager<StandardJavaFileManager> {

    private final ClassLookup lookup;

    ConfinedClassPath(StandardJavaFileManager standard, ClassLookup lookup) {
        super(standard);
        this.lookup = lookup;
    }

    @Override
    public Iterable<JavaFileObject> list(Location location, String packageName,
                                         Set<JavaFileObject.Kind> kinds, boolean recurse) throws IOException {
        if (location != StandardLocation.CLASS_PATH) {
            return super.list(location, packageName, kinds, recurse);
        }
        // A class is looked up by the package it is in; nothing asks the class path for the
        // packages below one, so `recurse` is not something this needs to answer.
        List<JavaFileObject> classes = new ArrayList<>();
        if (kinds.contains(JavaFileObject.Kind.CLASS)) {
            for (ClassLookup.Held held : lookup.classesIn(packageName)) {
                try {
                    classes.add(new HeldClass(held));
                } catch (URISyntaxException _) {
                    // A name that cannot be spelled as a location is not a class javac could ask for.
                }
            }
        }
        return classes;
    }

    @Override
    public String inferBinaryName(Location location, JavaFileObject file) {
        return file instanceof HeldClass held ? held.binaryName : super.inferBinaryName(location, file);
    }

    @Override
    public boolean isSameFile(FileObject a, FileObject b) {
        return a instanceof HeldClass || b instanceof HeldClass ? a == b : super.isSameFile(a, b);
    }

    @Override
    public boolean hasLocation(Location location) {
        return location == StandardLocation.CLASS_PATH || super.hasLocation(location);
    }

    /** A class file of the lookup. */
    private static final class HeldClass extends SimpleJavaFileObject {

        private final String binaryName;
        private final ClassLookup.Bytes bytes;

        HeldClass(ClassLookup.Held held) throws URISyntaxException {
            super(new URI("souther-classpath", "", "/" + held.binaryName().replace('.', '/') + ".class", null),
                    Kind.CLASS);
            this.binaryName = held.binaryName();
            this.bytes = held.bytes();
        }

        @Override
        public InputStream openInputStream() throws IOException {
            return new ByteArrayInputStream(bytes.get());
        }
    }
}
