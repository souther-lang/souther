package souther.compiler.jvm;

/**
 * What every {@link GeneratedClass} case refuses in the same words, so an identity with a hole in it
 * is refused where it is built rather than arriving later as a class name with a hole in it.
 */
final class Require {

    private Require() {}

    static void module(String module) {
        if (module == null || module.isEmpty()) {
            throw new IllegalArgumentException("a generated class belongs to a module");
        }
    }

    static void named(String module, String name) {
        module(module);
        if (name == null || name.isEmpty()) {
            throw new IllegalArgumentException("a generated class stands for something named");
        }
    }

    static void derivedFrom(GeneratedClass of) {
        if (of == null) {
            throw new IllegalArgumentException("a derived class is derived from a class");
        }
    }
}
