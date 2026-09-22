package souther.compiler.codegen;

import souther.compiler.types.Type;

import java.lang.classfile.CodeBuilder;
import java.lang.constant.ClassDesc;
import java.lang.constant.DirectMethodHandleDesc;
import java.lang.constant.DynamicCallSiteDesc;
import java.lang.constant.MethodHandleDesc;
import java.lang.constant.MethodTypeDesc;

import static souther.compiler.codegen.Descriptors.*;

/**
 * Canonicalizes a value of a declared {@code Type}, wherever it just crossed from outside the
 * compiler's own reach into a Souther value: an injected behavior's answer
 * ({@code BodyGen.requiredCall}), the argument a Java caller hands a generated behavior's public
 * {@code apply} ({@code Backend.generateSpecFn}), and the field a Java-supplied factory
 * ({@code Backend.emitDataFactory}) hands {@code __construct}. A decoder's own leaf
 * ({@code CodecGen.emitStringLeaf}) and the compiler's two original boundary doors
 * ({@code Reserved.name}/{@code CanonicalNames.name}, a source literal) are the same invariant
 * established a different way and are not this class's business.
 *
 * <p>{@code String} is the leaf; {@code List}/{@code Set}/{@code Option}/{@code Map} are walked
 * recursively, the same shapes {@link CodecGen}'s encoder side already composes a nested
 * {@code Function} for — this is the identical technique turned around: instead of composing an
 * {@code Encoder}, it composes the plain {@code java.util.function.Function} the runtime's
 * {@code Lists.map}/{@code Sets.map}/{@code Options.mapWith}/{@code Maps.mapValuesWith} take, built
 * once per crossing at codegen time from the declared {@code Type} and applied to the value already
 * on the stack.
 *
 * <p>Not walked into a data's own field, into a {@code Type.Union}'s members, or into a
 * {@code Map}'s key or value when that {@code Map} itself sits inside another container: the first
 * two are the same scope boundary {@link CodecGen}'s decoder side draws (construction and container
 * recursion are two questions); the third is this class's own — a {@code Map} composes two
 * functions (key and value) rather than one, and nesting that pair inside another container's single
 * captured function is a second kind of composition this does not build. A {@code List<String>}
 * crossing this door is canonicalized; a {@code List<Map<String, String>>} is not — a narrower,
 * named gap, not a silent one.
 */
final class CanonicalizeAtCrossing {

    private CanonicalizeAtCrossing() {}

    /** Whether {@code type} is {@code String}, or reaches one through a container this recurses
     *  into — the same structural test the closed-world kernel classification test states over a
     *  kernel's declared result, applied here to an arbitrary crossing's declared type. */
    static boolean reachesString(Type type) {
        return switch (type) {
            case Type.Prim p -> p == Type.STRING;
            case Type.ListOf t -> reachesString(t.element());
            case Type.SetOf t -> reachesString(t.element());
            case Type.OptionOf t -> reachesString(t.element());
            case Type.MapOf t -> reachesString(t.key()) || reachesString(t.value());
            default -> false;
        };
    }

    /** Canonicalizes the {@code Object} on top of the stack in place, leaving the canonicalized
     *  {@code Object} on top of the stack — a no-op, structurally, wherever {@link #reachesString}
     *  says {@code type} does not reach one. */
    static void emit(CodeBuilder code, Type type) {
        switch (type) {
            case Type.Prim p when p == Type.STRING -> {
                code.checkcast(CD_String);
                code.invokestatic(CD_Normalization, "nfc", MTD_nfc);
            }
            case Type.ListOf t when reachesString(t.element()) -> {
                code.checkcast(CD_List);
                emitAsFunction(code, t.element());
                code.swap();   // Lists.map(Function, List): pushed [list, fn], the call wants [fn, list]
                code.invokestatic(CD_Lists, "map", MTD_Lists_map);
            }
            case Type.SetOf t when reachesString(t.element()) -> {
                code.checkcast(CD_Set);
                emitAsFunction(code, t.element());
                code.swap();
                code.invokestatic(CD_Sets, "map", MTD_Sets_map);
            }
            case Type.OptionOf t when reachesString(t.element()) -> {
                code.checkcast(CD_Option);
                emitAsFunction(code, t.element());
                code.swap();
                code.invokestatic(CD_Options, "mapWith", MTD_optionMapWith);
            }
            case Type.MapOf t -> {
                code.checkcast(CD_Map);
                if (reachesString(t.key())) {
                    emitAsFunction(code, t.key());
                    code.swap();
                    code.invokestatic(CD_Maps, "mapKeysWith", MTD_mapKeysWith);
                }
                if (reachesString(t.value())) {
                    emitAsFunction(code, t.value());
                    code.swap();
                    code.invokestatic(CD_Maps, "mapValuesWith", MTD_mapValuesWith);
                }
            }
            default -> { }   // does not reach String: the value is left untouched
        }
    }

    /** Pushes a {@code Function<Object, Object>} implementing {@link #emit} for {@code type}, for a
     *  container's element canonicalization to compose recursively. A leaf {@code String} is the
     *  one no-capture case ({@code Normalization::nfc} directly); a compound case first recurses to
     *  push the function it composes into, then captures that function in an
     *  {@code invokedynamic} — the same capturing technique {@code CodecGen}'s
     *  {@code mapKeysCallSite} already uses for the encoder side, generalized to any one of
     *  {@code Lists.map}/{@code Sets.map}/{@code Options.mapWith}. */
    private static void emitAsFunction(CodeBuilder code, Type type) {
        if (type instanceof Type.Prim p && p == Type.STRING) {
            code.invokedynamic(DynamicCallSiteDesc.of(
                    BSM_METAFACTORY, "apply",
                    MethodTypeDesc.of(CD_Function),                          // no captures
                    MethodTypeDesc.of(CD_Object, CD_Object),                 // samMethodType
                    MethodHandleDesc.ofMethod(
                            DirectMethodHandleDesc.Kind.STATIC, CD_Normalization, "nfc", MTD_nfc),
                    MTD_nfc));
            return;
        }
        Type element = switch (type) {
            case Type.ListOf t -> t.element();
            case Type.SetOf t -> t.element();
            case Type.OptionOf t -> t.element();
            default -> throw new IllegalArgumentException(
                    "canonicalizeAtCrossing does not compose a Function for " + type
                            + " as a container's element — a Map here would need two captured"
                            + " functions (key and value), which is a second kind of composition"
                            + " this does not build");
        };
        emitAsFunction(code, element);
        ClassDesc runtime;
        String method;
        MethodTypeDesc mtd;
        ClassDesc container;
        if (type instanceof Type.ListOf) {
            runtime = CD_Lists;
            method = "map";
            mtd = MTD_Lists_map;
            container = CD_List;
        } else if (type instanceof Type.SetOf) {
            runtime = CD_Sets;
            method = "map";
            mtd = MTD_Sets_map;
            container = CD_Set;
        } else {
            runtime = CD_Options;
            method = "mapWith";
            mtd = MTD_optionMapWith;
            container = CD_Option;
        }
        code.invokedynamic(DynamicCallSiteDesc.of(
                BSM_METAFACTORY, "apply",
                MethodTypeDesc.of(CD_Function, CD_Function),                 // captures the element Function
                MethodTypeDesc.of(CD_Object, CD_Object),                     // samMethodType
                MethodHandleDesc.ofMethod(DirectMethodHandleDesc.Kind.STATIC, runtime, method, mtd),
                MethodTypeDesc.of(container, container)));                  // instantiatedMethodType
    }
}
