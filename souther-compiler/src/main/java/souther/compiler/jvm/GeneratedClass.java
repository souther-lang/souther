package souther.compiler.jvm;

import souther.compiler.types.TypeName;

/**
 * A JVM class this compiler invents, said in Souther's terms: which declaration it stands for and
 * what it is to that declaration. Not a name — {@link SoutherJvmAbi#nameOf} is the one place that
 * turns one of these into a spelling.
 *
 * <p>Each case takes exactly what it needs to be one class and nothing else, because what identifies
 * a generated class differs by what it is. A value class is a declared type. A behavior's
 * implementation is a behavior of the module that declares it. A bridge case is a member and the
 * module that emits the case for it, which is not the member's own module and is the distinction a
 * reader assembling {@code module + "." + member.name() + "Case"} loses. One record carrying a role
 * enum beside every field any role might want would admit a lambda with a member and a module class
 * with a name, and those states mean nothing.
 *
 * <p>A codec and a compile-time evaluator are derived from another generated class rather than from a
 * name, so they hold that class: the encoder of a behavior's result union is
 * {@code Encoder(BehaviorResult(m, foo))}, and a caller never has to know that the union is called
 * {@code FooResult} in order to ask for the encoder beside it.
 */
public sealed interface GeneratedClass {

    /** The class a declared data, sum or unit type is emitted as. */
    record Value(TypeName type) implements GeneratedClass {
        public Value {
            if (type == null) {
                throw new IllegalArgumentException("a value class stands for a declared type");
            }
        }
    }

    /** The interface a behavior is declared as, in the module that declares the behavior. */
    record BehaviorInterface(String module, String behavior) implements GeneratedClass {
        public BehaviorInterface {
            Require.named(module, behavior);
        }
    }

    /** The class holding a fn/pipe behavior's fields, constructor and erased {@code apply} — what a
     *  caller entering a compiled behavior loads. An injected behavior has none. */
    record BehaviorImpl(String module, String behavior) implements GeneratedClass {
        public BehaviorImpl {
            Require.named(module, behavior);
        }
    }

    /** The sealed interface a behavior's anonymous union output is emitted as, in the module that
     *  declares the behavior. */
    record BehaviorResult(String module, String behavior) implements GeneratedClass {
        public BehaviorResult {
            Require.named(module, behavior);
        }
    }

    /**
     * The record a union member reaches its result unions through, emitted by the module that holds
     * the union.
     *
     * <p>{@code emittingModule} is that module, and it is not the member's. A member declared
     * elsewhere, or a primitive, is bridged by whoever unions it, so the same member reached from two
     * modules is two classes. Reading the module off the reader instead is right exactly when the
     * reader happens to be the emitter.
     */
    record BridgeCase(String emittingModule, TypeName member) implements GeneratedClass {
        public BridgeCase {
            if (emittingModule == null || emittingModule.isEmpty() || member == null) {
                throw new IllegalArgumentException("a bridge case is a member and the module emitting it: "
                        + emittingModule + ", " + member);
            }
        }
    }

    /** The derived encoder beside the class it encodes. */
    record Encoder(GeneratedClass of) implements GeneratedClass {
        public Encoder {
            Require.derivedFrom(of);
        }
    }

    /** One of the derived decoders beside the class it builds. */
    record Decoder(GeneratedClass of, DecoderKind kind) implements GeneratedClass {
        public Decoder {
            Require.derivedFrom(of);
            if (kind == null) {
                throw new IllegalArgumentException("which decoder is part of what it is called");
            }
        }
    }

    /** The class carrying a type's compile-time evaluation entry point. */
    record Ctfe(GeneratedClass of) implements GeneratedClass {
        public Ctfe {
            Require.derivedFrom(of);
        }
    }

    /** The class a module's own declarations are published on. It carries nothing but them. */
    record ModuleDeclarations(String module) implements GeneratedClass {
        public ModuleDeclarations {
            Require.module(module);
        }
    }

    /** The class a module's recursive helpers are lowered onto as static methods. */
    record Helpers(String module) implements GeneratedClass {
        public Helpers {
            Require.module(module);
        }
    }

    /**
     * The stand-in an example builds for an injected behavior it has to answer for: a subclass of
     * that behavior's base, defined into the run rather than emitted with the module.
     *
     * <p>Not part of what a module ships, and here anyway. It is a class this compiler invents and
     * then loads by name, which is the whole of what makes a name a rule two places can disagree
     * about.
     */
    record ExampleFake(GeneratedClass of) implements GeneratedClass {
        public ExampleFake {
            Require.derivedFrom(of);
        }
    }

    /** A synthetic class for an escaping lambda, numbered within the module that emits it. */
    record Lambda(String module, int id) implements GeneratedClass {
        public Lambda {
            Require.module(module);
            if (id < 0) {
                throw new IllegalArgumentException("a lambda is numbered from zero: " + id);
            }
        }
    }

}
