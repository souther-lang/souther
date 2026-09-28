package souther.compiler.jvm;

import souther.compiler.types.TypeKey;
import souther.compiler.types.ValueName;

/**
 * A declaration another module's classes can link against: a behavior, a declared type, or a
 * published value.
 *
 * <p>The unit a compiled module's linkage is recorded in. A class compiled against a module assumes
 * facts about some of its declarations and none about the rest, so what it assumed is said per
 * declaration: an edit to a declaration nothing linked against leaves every class built against the
 * module as it was.
 *
 * <p>Ordered by kind, then module, then name, which is the order an artifact writes them in.
 */
public sealed interface LinkageTarget extends Comparable<LinkageTarget> {

    /** The module that declares it. */
    String module();

    /** The name it is declared under. */
    String name();

    /** The word an artifact writes before the module and the name, to say which kind it is. */
    String kind();

    /** A behavior, whichever of its classes is linked against. */
    record Behavior(ValueName.Behavior behavior) implements LinkageTarget {
        public Behavior {
            if (behavior == null) {
                throw new IllegalArgumentException("a behavior is what this is");
            }
        }

        @Override
        public String module() {
            return behavior.module();
        }

        @Override
        public String name() {
            return behavior.name();
        }

        @Override
        public String kind() {
            return "behavior";
        }
    }

    /** A data, sum or unit declaration, whichever of its classes is linked against. */
    record Data(TypeKey key) implements LinkageTarget {
        public Data {
            if (key == null) {
                throw new IllegalArgumentException("a declared type is what this is");
            }
        }

        @Override
        public String module() {
            return key.module();
        }

        @Override
        public String name() {
            return key.name();
        }

        @Override
        public String kind() {
            return "data";
        }
    }

    /** A published value, which runs where it is declared and is called through its entry there. */
    record Value(ValueName.Helper value) implements LinkageTarget {
        public Value {
            if (value == null) {
                throw new IllegalArgumentException("a published value is what this is");
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

    /** The target an artifact wrote as {@code kind}, {@code module} and {@code name}, or null where
     *  {@code kind} is no word this writes. */
    static LinkageTarget readingWritten(String kind, String module, String name) {
        return switch (kind) {
            case "behavior" -> new Behavior(new ValueName.Behavior(module, name));
            case "data" -> new Data(new TypeKey(module, name));
            case "value" -> new Value(new ValueName.Helper(module, name));
            default -> null;
        };
    }

    @Override
    default int compareTo(LinkageTarget other) {
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
