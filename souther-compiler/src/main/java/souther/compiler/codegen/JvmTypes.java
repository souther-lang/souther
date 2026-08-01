package souther.compiler.codegen;

import souther.compiler.types.Type;
import java.lang.classfile.Annotation;
import java.lang.classfile.ClassBuilder;
import java.lang.classfile.ClassFile;
import java.lang.classfile.CodeBuilder;
import java.lang.classfile.Label;
import java.lang.classfile.TypeAnnotation;
import java.lang.constant.ClassDesc;
import java.lang.constant.ConstantDescs;
import java.lang.constant.MethodTypeDesc;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.function.Consumer;

import static souther.compiler.codegen.Descriptors.*;

/**
 * Type-shaped bytecode helpers. The first group depends on nothing but the {@link Type} and the
 * descriptors: how a value is boxed, loaded, stored, and how wide its JVM slot is. The second group
 * ({@code jvmType}/{@code fieldDescs}/{@code unbox}/{@code castFromObject}) resolves a data name to a
 * class through the module's package map, so each takes a {@link CodegenContext} to reach
 * {@code caseClass}.
 */
final class JvmTypes {

    private JvmTypes() {
    }

    /** Boxes an {@code Int}/{@code Bool} on the stack; a no-op for a reference, already an Object. */
    static void box(CodeBuilder code, Type type) {
        if (type == Type.INT) {
            code.invokestatic(CD_Long, "valueOf", MTD_Long_valueOf);
        } else if (type == Type.BOOL) {
            code.invokestatic(CD_Boolean, "valueOf", MTD_Boolean_valueOf);
        }
    }

    /** The boxed JVM class for a primitive type, or {@code null} for a non-primitive. */
    static ClassDesc boxedPrim(Type t) {
        if (t == Type.INT) return CD_Long;
        if (t == Type.BOOL) return CD_Boolean;
        if (t == Type.DECIMAL) return CD_BigDecimal;
        if (t == Type.STRING) return CD_String;
        if (t == Type.DATE) return CD_LocalDate;
        if (t == Type.DATETIME) return CD_LocalDateTime;
        return null;
    }

    /** True when {@code t} is carried as a reference on the JVM (everything but Int and Bool). */
    static boolean isReference(Type t) {
        return t != Type.INT && t != Type.BOOL;
    }

    static void load(CodeBuilder code, int slot, Type type) {
        if (type == Type.INT) {
            code.lload(slot);
        } else if (type == Type.BOOL) {
            code.iload(slot);
        } else {
            code.aload(slot); // String or a data reference
        }
    }

    static void store(CodeBuilder code, int slot, Type type) {
        if (type == Type.INT) {
            code.lstore(slot);
        } else if (type == Type.BOOL) {
            code.istore(slot);
        } else {
            code.astore(slot);
        }
    }

    static void pushInt(CodeBuilder code, int v) {
        switch (v) {
            case 0 -> code.iconst_0();
            case 1 -> code.iconst_1();
            case 2 -> code.iconst_2();
            case 3 -> code.iconst_3();
            case 4 -> code.iconst_4();
            case 5 -> code.iconst_5();
            default -> code.loadConstant(Integer.valueOf(v));
        }
    }

    /** The JVM slot width of {@code type}: an {@code Int} is a {@code long} (two slots), else one. */
    static int width(Type type) {
        return type == Type.INT ? 2 : 1;
    }

    /** Emits a package-private default constructor that chains to {@code Object.<init>}. */
    static void emitDefaultCtor(ClassBuilder cb) {
        emitDefaultCtor(cb, CD_Object);
    }

    /** Emits a package-private default constructor that chains to {@code superCd}'s. */
    static void emitDefaultCtor(ClassBuilder cb, ClassDesc superCd) {
        cb.withMethodBody("<init>", MTD_void, 0, code -> {
            code.aload(0);
            code.invokespecial(superCd, "<init>", MTD_void);
            code.return_();
        });
    }

    /** Emits a {@code public} default constructor that chains to {@code Object.<init>}. */
    static void emitPublicCtor(ClassBuilder cb) {
        cb.withMethodBody("<init>", MTD_void, ClassFile.ACC_PUBLIC, code -> {
            code.aload(0);
            code.invokespecial(CD_Object, "<init>", MTD_void);
            code.return_();
        });
    }

    /** The field a class with no state holds its one instance in; {@link #loadSharedInstance} reads it. */
    private static final String SHARED_INSTANCE = "INSTANCE";

    /**
     * Gives a class with no state one instance of itself, so every use site loads it instead of
     * allocating: a unit data, a lambda that captures nothing, a decoder/encoder implementation.
     *
     * <p>{@code extraInit} folds any other static setup into the single {@code <clinit>} a class may
     * carry — a second one is a duplicate method and a {@code ClassFormatError} at load time. This is
     * the only place in the backend that writes a {@code <clinit>}, which is what keeps that true.
     */
    static void emitSharedInstance(ClassBuilder cb, ClassDesc cd, int fieldFlags,
                                   Consumer<CodeBuilder> extraInit) {
        cb.withField(SHARED_INSTANCE, cd, fieldFlags | ClassFile.ACC_STATIC | ClassFile.ACC_FINAL);
        cb.withMethodBody(ConstantDescs.CLASS_INIT_NAME, MTD_void, ClassFile.ACC_STATIC, code -> {
            if (extraInit != null) {
                extraInit.accept(code);
            }
            code.new_(cd);
            code.dup();
            code.invokespecial(cd, "<init>", MTD_void);
            code.putstatic(cd, SHARED_INSTANCE, cd);
            code.return_();
        });
    }

    /** {@link #emitSharedInstance} with a {@code public} field and no other static setup. */
    static void emitSharedInstance(ClassBuilder cb, ClassDesc cd) {
        emitSharedInstance(cb, cd, ClassFile.ACC_PUBLIC, null);
    }

    /** Loads the one instance {@link #emitSharedInstance} gave {@code cd}. */
    static void loadSharedInstance(CodeBuilder code, ClassDesc cd) {
        code.getstatic(cd, SHARED_INSTANCE, cd);
    }

    /**
     * Emits value equality for two values on the stack, leaving a boolean.
     *
     * <p>What sameness means is the runtime's to say, so this calls {@code Values.equal} rather than
     * emitting the rule a second time. {@code decimal} picks the overload the static type allows: a
     * pair of Decimals goes to the one that takes them, which skips the tests the general form makes
     * to find out what it was handed.
     *
     * <p>{@code BigDecimal.equals} also compares the scale, so it calls 1.0 and 1.00 different.
     * Scale is how a number was written, not what it is (spec 7.1): the same amount arrives with
     * a different scale depending on whether it was read from JSON or a DB column, and a money
     * type whose equality turns on that is a trap. Clojure, Scala and Ceylon all chose the same way.
     */
    static void emitValueEquals(CodeBuilder code, boolean decimal) {
        if (decimal) {
            code.invokestatic(CD_Values, "equal", MTD_Values_equalDecimal);
        } else {
            code.invokestatic(CD_Values, "equal", MTD_Values_equal);
        }
    }

    /** Emits the hash that agrees with {@link #emitValueEquals}, for a value on the stack. */
    static void emitValueHash(CodeBuilder code, boolean decimal) {
        if (decimal) {
            code.invokestatic(CD_Values, "hash", MTD_Values_hashDecimal);
        } else {
            code.invokestatic(CD_Values, "hash", MTD_Values_hash);
        }
    }

    // --- reference-resolving members: these reach the module's package map through the context ---

    /** The JVM class carrying a value of {@code type}: primitives unboxed, containers as their raw
     * interface, a data reference through {@link CodegenContext#caseClass}. */
    static ClassDesc jvmType(Type type, CodegenContext ctx) {
        if (type == Type.INT) return ConstantDescs.CD_long;
        if (type == Type.STRING) return CD_String;
        if (type == Type.BOOL) return ConstantDescs.CD_boolean;
        if (type == Type.DECIMAL) return CD_BigDecimal;
        if (type == Type.DATE) return CD_LocalDate;
        if (type == Type.DATETIME) return CD_LocalDateTime;
        if (type instanceof Type.OptionOf) return CD_Option;
        if (type instanceof Type.ListOf) return CD_List;
        if (type instanceof Type.MapOf) return CD_Map;
        if (type instanceof Type.SetOf) return CD_Set;
        if (type instanceof Type.Union) return CD_Object;
        if (type instanceof Type.Var) return CD_Object;   // a type variable is erased to Object
        if (type instanceof Type.Nothing) return CD_Object;   // an empty collection's element bottom
        if (type instanceof Type.FnOf) return CD_Fn;
        if (type instanceof Type.TupleOf) return CD_Object.arrayType();   // a tuple is an Object[]
        return ctx.caseClass(((Type.Ref) type).name());
    }

    static ClassDesc[] fieldDescs(Map<String, Type> fields, CodegenContext ctx) {
        List<ClassDesc> descs = new ArrayList<>();
        for (Type t : fields.values()) {
            descs.add(jvmType(t, ctx));
        }
        return descs.toArray(new ClassDesc[0]);
    }

    /**
     * {@code @NonNull} for every reference position of {@code type} at {@code target}: the type itself
     * and, for a container, each type argument down to the innermost element ({@code List<Map<K,V>>}
     * annotates four positions). A type argument is always a reference — an {@code Int} element is a
     * {@code Long} — so only a primitive at the root has no position at all, and that root returns an
     * empty list.
     *
     * <p>{@code @NullMarked} on the class says the same thing once, and a Kotlin reader acts on it for
     * every member except a record component's accessor, which it types from the component and so
     * reaches without applying the marking. Those accessors carry this instead (spec §jvm-nullness).
     */
    static List<TypeAnnotation> nonNullPositions(Type type, TypeAnnotation.TargetInfo target) {
        List<TypeAnnotation> out = new ArrayList<>();
        if (type != Type.INT && type != Type.BOOL) {
            collectNonNull(type, List.of(), target, out);
        }
        return out;
    }

    private static void collectNonNull(Type type, List<TypeAnnotation.TypePathComponent> path,
                                       TypeAnnotation.TargetInfo target, List<TypeAnnotation> out) {
        out.add(TypeAnnotation.of(target, path, Annotation.of(CD_NonNull)));
        switch (type) {
            case Type.ListOf l -> collectNonNull(l.element(), typeArgument(path, 0), target, out);
            case Type.SetOf s -> collectNonNull(s.element(), typeArgument(path, 0), target, out);
            case Type.OptionOf o -> collectNonNull(o.element(), typeArgument(path, 0), target, out);
            case Type.MapOf m -> {
                collectNonNull(m.key(), typeArgument(path, 0), target, out);
                collectNonNull(m.value(), typeArgument(path, 1), target, out);
            }
            default -> {
            }
        }
    }

    /** {@code path} extended to reach the {@code index}-th type argument of the type it names. */
    private static List<TypeAnnotation.TypePathComponent> typeArgument(
            List<TypeAnnotation.TypePathComponent> path, int index) {
        List<TypeAnnotation.TypePathComponent> deeper = new ArrayList<>(path);
        deeper.add(TypeAnnotation.TypePathComponent.of(
                TypeAnnotation.TypePathComponent.Kind.TYPE_ARGUMENT, index));
        return List.copyOf(deeper);
    }

    /**
     * The generic type signature for a container-typed field or accessor
     * ({@code List<E>} / {@code Set<E>} / {@code Map<K,V>} / {@code Option<E>}), or {@code null} for a
     * type whose raw descriptor already names it fully (a scalar, a data reference, a union). Attached
     * as a {@code Signature} attribute so a Java consumer recovers the element type instead of a raw
     * {@code List} it has to cast out of.
     */
    static String genericSig(Type type, CodegenContext ctx) {
        return switch (type) {
            case Type.ListOf l -> "Ljava/util/List<" + refSig(l.element(), ctx) + ">;";
            case Type.SetOf s -> "Ljava/util/Set<" + refSig(s.element(), ctx) + ">;";
            case Type.OptionOf o -> "Lsouther/runtime/Option<" + refSig(o.element(), ctx) + ">;";
            case Type.MapOf m -> "Ljava/util/Map<" + refSig(m.key(), ctx) + refSig(m.value(), ctx) + ">;";
            default -> null;
        };
    }

    /**
     * An element type's signature as a reference (generic arguments are never primitive, so a
     * primitive element takes its boxed class — {@code Int} is {@code Long}, {@code Bool} is
     * {@code Boolean}). A nested container recurses ({@code List<List<E>>}); any other type's raw
     * descriptor is already a reference.
     */
    private static String refSig(Type element, CodegenContext ctx) {
        String nested = genericSig(element, ctx);
        if (nested != null) return nested;
        ClassDesc boxed = boxedPrim(element);
        return (boxed != null ? boxed : jvmType(element, ctx)).descriptorString();
    }

    /** Unboxes/casts the {@code Object} on the stack to {@code type}'s JVM form and stores it in
     * {@code slot}. */
    static void unbox(CodeBuilder code, Type type, int slot, CodegenContext ctx) {
        if (type == Type.INT) {
            code.checkcast(CD_Long);
            code.invokevirtual(CD_Long, "longValue", MethodTypeDesc.of(ConstantDescs.CD_long));
            code.lstore(slot);
        } else if (type == Type.BOOL) {
            code.checkcast(CD_Boolean);
            code.invokevirtual(CD_Boolean, "booleanValue", MethodTypeDesc.of(ConstantDescs.CD_boolean));
            code.istore(slot);
        } else {
            code.checkcast(jvmType(type, ctx));
            code.astore(slot);
        }
    }

    /** Casts the {@code Object} on the stack to {@code type}'s JVM form, unboxing Int/Bool — the
     * stack-only counterpart of {@link #unbox}, used to read a boxed tuple element (ADR-0036). */
    static void castFromObject(CodeBuilder code, Type type, CodegenContext ctx) {
        if (type == Type.INT) {
            code.checkcast(CD_Long);
            code.invokevirtual(CD_Long, "longValue", MethodTypeDesc.of(ConstantDescs.CD_long));
        } else if (type == Type.BOOL) {
            code.checkcast(CD_Boolean);
            code.invokevirtual(CD_Boolean, "booleanValue", MethodTypeDesc.of(ConstantDescs.CD_boolean));
        } else {
            code.checkcast(jvmType(type, ctx));
        }
    }
}
