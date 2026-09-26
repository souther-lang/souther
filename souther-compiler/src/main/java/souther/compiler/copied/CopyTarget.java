package souther.compiler.copied;

import souther.compiler.types.ReachName;
import souther.compiler.types.TypeKey;
import souther.compiler.types.ValueName;

/**
 * A declaration another module's classes can carry a copy of: a helper, a value, or a type's
 * invariant.
 *
 * <p>The unit what a module copied is recorded in, as {@link souther.compiler.jvm.LinkageTarget} is
 * the unit of what it links against. A copy leaves nothing in the classes that names the declaration,
 * so what was copied is said per declaration, and an edit to a declaration nothing copied leaves every
 * module built against it as it was.
 *
 * <p>Always the declaration the fact came from and never where it landed. A decoder carrying a pattern
 * an invariant names requires the invariant: which class the copy ended up in is how the emitter
 * works and says nothing about what the classes were built against.
 *
 * <p>Ordered by kind, then module, then name, which is the order an artifact writes them in.
 */
public sealed interface CopyTarget extends Comparable<CopyTarget> {

    /** The module that declares it. */
    String module();

    /** The name it is declared under. */
    String name();

    /** The word an artifact writes before the module and the name, to say which kind it is. */
    String kind();

    /** A helper, expanded where it is called or emitted as a method of the reader. */
    record Helper(ValueName.Helper helper) implements CopyTarget {
        public Helper {
            if (helper == null) {
                throw new IllegalArgumentException("a helper is what this is");
            }
        }

        @Override
        public String module() {
            return helper.module();
        }

        @Override
        public String name() {
            return helper.name();
        }

        @Override
        public String kind() {
            return "helper";
        }
    }

    /** A value, whose constant or whose body a reader carries. */
    record Value(ValueName.Helper value) implements CopyTarget {
        public Value {
            if (value == null) {
                throw new IllegalArgumentException("a value is what this is");
            }
        }

        @Override
        public String module() {
            return value.module();
        }

        @Override
        public String name() {
            return value.name();
        }

        @Override
        public String kind() {
            return "value";
        }
    }

    /** The invariant of a declared type, checked by every type that includes it. */
    record Invariant(TypeKey type) implements CopyTarget {
        public Invariant {
            if (type == null) {
                throw new IllegalArgumentException("a declared type is what this is");
            }
        }

        @Override
        public String module() {
            return type.module();
        }

        @Override
        public String name() {
            return type.name();
        }

        @Override
        public String kind() {
            return "invariant";
        }
    }

    /**
     * What {@code reaches} names, where it is a definition a module compiled as {@code here} would
     * be copying — or null.
     *
     * <p>A definition of {@code here} is not a copy: a module is built against its own declarations
     * by being built. Nor is one of the language's own, which is the same on every side of every
     * artifact.
     */
    static ValueName.Helper declaredElsewhere(ReachName.Declaration reaches, String here) {
        return reaches instanceof ReachName.OfModule of
                && of.denotes() instanceof ValueName.Helper declared
                && !declared.module().equals(here) && !declared.isDeclaredByLanguage()
                ? declared : null;
    }

    /** The target an artifact wrote as {@code kind}, {@code module} and {@code name}, or null where
     *  {@code kind} is no word this writes. */
    static CopyTarget readingWritten(String kind, String module, String name) {
        return switch (kind) {
            case "helper" -> new Helper(new ValueName.Helper(module, name));
            case "value" -> new Value(new ValueName.Helper(module, name));
            case "invariant" -> new Invariant(new TypeKey(module, name));
            default -> null;
        };
    }

    @Override
    default int compareTo(CopyTarget other) {
        int byKind = kind().compareTo(other.kind());
        if (byKind != 0) {
            return byKind;
        }
        int byModule = module().compareTo(other.module());
        return byModule != 0 ? byModule : name().compareTo(other.name());
    }

    /** How a report names it: the module and the name. */
    default String shown() {
        return module() + "." + name();
    }
}
