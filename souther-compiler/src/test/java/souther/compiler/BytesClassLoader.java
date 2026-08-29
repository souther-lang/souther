package souther.compiler;

import souther.compiler.jvm.ClassFileImage;

import java.util.Map;

/**
 * Loads Souther-generated classes from an in-memory class-file map. Runtime classes
 * (Raw, Result, Decoder, ...) resolve through the parent, so a cast of a generated
 * value to a runtime interface is type-compatible across the two loaders.
 */
final class BytesClassLoader extends ClassLoader {

    private final Map<String, ClassFileImage> classes;

    BytesClassLoader(Map<String, ClassFileImage> classes, ClassLoader parent) {
        super(parent);
        this.classes = classes;
    }

    @Override
    protected Class<?> findClass(String name) throws ClassNotFoundException {
        ClassFileImage image = classes.get(name);
        if (image == null) {
            throw new ClassNotFoundException(name);
        }
        byte[] bytes = image.bytes();
        return defineClass(name, bytes, 0, bytes.length);
    }
}
