package souther.compiler.codegen;

import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.lang.classfile.CodeBuilder;
import java.lang.classfile.Label;
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
 * {@code apply} ({@code Backend.generateSpecFn}), a composition's own arguments and each stage's
 * answer ({@code Backend.generatePipe}), the field a Java-supplied factory
 * ({@code Backend.emitDataFactory}) hands {@code __construct}, and the arguments and answer an
 * {@code ensures} check reads at a crossing ({@code Backend.emitCheckingApply}). A decoder's own
 * leaf ({@code CodecGen.emitStringLeaf}) and the compiler's two original boundary doors
 * ({@code Reserved.name}/{@code CanonicalNames.name}, a source literal) are the same invariant
 * established a different way and are not this class's business.
 *
 * <p>{@code String} is the leaf; {@code List}/{@code Set}/{@code Option}/{@code Map} are walked
 * recursively, the same shapes {@link CodecGen}'s encoder side already composes a nested
 * {@code Function} for — this is the identical technique turned around: instead of composing an
 * {@code Encoder}, it composes the plain {@code java.util.function.Function} the runtime's
 * {@code Lists.map}/{@code Sets.map}/{@code Options.mapWith}/{@code Maps.canonicalizeWith} take,
 * built once per crossing at codegen time from the declared {@code Type} and applied to the value
 * already on the stack. A {@code Type.Union} carrying a bare {@code String} member is read at run
 * time, the one place this cannot be settled at codegen time: an {@code instanceof String} guards
 * the canonicalization, since which member a crossing value actually is is not known until then.
 *
 * <p>Not walked into a data's own field, or into a {@code Type.Union} member other than a bare
 * {@code String} — the same scope boundary {@link CodecGen}'s decoder side draws between
 * construction and container recursion. A {@code Map}'s key canonicalization can collide (two
 * distinct keys becoming one), which {@link souther.runtime.Maps#canonicalizeWith} refuses rather
 * than silently dropping an entry, the same way a derived decoder refuses a {@code duplicate_key}.
 */
final class CanonicalizeAtCrossing {

    private CanonicalizeAtCrossing() {}

    /** Whether {@code type} is {@code String}, reaches one through a container this recurses into,
     *  or is a union naming {@code String} as a bare member — the same structural test the
     *  closed-world kernel classification test states over a kernel's declared result, applied here
     *  to an arbitrary crossing's declared type. */
    static boolean reachesString(Type type) {
        return switch (type) {
            case Type.Prim p -> p == Type.STRING;
            case Type.ListOf t -> reachesString(t.element());
            case Type.SetOf t -> reachesString(t.element());
            case Type.OptionOf t -> reachesString(t.element());
            case Type.MapOf t -> reachesString(t.key()) || reachesString(t.value());
            case Type.Union u -> unionHasBareStringMember(u);
            default -> false;
        };
    }

    private static boolean unionHasBareStringMember(Type.Union u) {
        for (TypeSymbol member : u.members()) {
            if (member instanceof TypeSymbol.Primitive p && p.primitive() == Type.STRING) {
                return true;
            }
        }
        return false;
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
            case Type.MapOf t when reachesString(t.key()) || reachesString(t.value()) -> {
                // Pushed in this order, [map, keyFn, valueFn] is already the call's own parameter
                // order (Map, Function, Function) — no reordering needed, unlike the three cases
                // above, each of which pushes its element function after a container that was
                // already on the stack before this method's own single Function parameter.
                code.checkcast(CD_Map);
                emitFunctionOrIdentity(code, t.key());
                emitFunctionOrIdentity(code, t.value());
                code.invokestatic(CD_Maps, "canonicalizeWith", MTD_mapsCanonicalizeWith);
            }
            case Type.Union u when unionHasBareStringMember(u) -> {
                Label notString = code.newLabel();
                Label end = code.newLabel();
                code.dup();
                code.instanceOf(CD_String);
                code.ifeq(notString);
                code.checkcast(CD_String);
                code.invokestatic(CD_Normalization, "nfc", MTD_nfc);
                code.goto_(end);
                code.labelBinding(notString);
                code.labelBinding(end);
            }
            default -> { }   // does not reach String: the value is left untouched
        }
    }

    /** Pushes {@link #emitAsFunction} for {@code element}, or {@code Function.identity()} where
     *  {@link #reachesString} says there is nothing to canonicalize — a {@code Map}'s key and value
     *  are asked for independently, and only one of the two may reach a {@code String}. */
    private static void emitFunctionOrIdentity(CodeBuilder code, Type element) {
        if (reachesString(element)) {
            emitAsFunction(code, element);
        } else {
            code.invokestatic(CD_Function, "identity", MTD_functionIdentity, true);
        }
    }

    /** Pushes a {@code Function<Object, Object>} implementing {@link #emit} for {@code type}, for a
     *  container's element canonicalization to compose recursively. A leaf {@code String} is the
     *  one no-capture case ({@code Normalization::nfc} directly); a compound case first recurses to
     *  push the function(s) it composes into, then captures them in an {@code invokedynamic} — the
     *  same capturing technique {@code CodecGen}'s {@code mapKeysCallSite} already uses for the
     *  encoder side, generalized to any one of
     *  {@code Lists.map}/{@code Sets.map}/{@code Options.mapWith}/{@code Maps.canonicalizeWithCaptured}.
     *  Does not handle {@code Type.Union}: a union's own member is read at run time by {@link #emit},
     *  which this recursion has no call site for — a {@code List<String | Missing>} is a narrower
     *  gap than {@code List<String>} for that reason. */
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
        if (type instanceof Type.MapOf t) {
            emitFunctionOrIdentity(code, t.key());
            emitFunctionOrIdentity(code, t.value());
            code.invokedynamic(DynamicCallSiteDesc.of(
                    BSM_METAFACTORY, "apply",
                    MethodTypeDesc.of(CD_Function, CD_Function, CD_Function),   // captures key, value
                    MethodTypeDesc.of(CD_Object, CD_Object),                   // samMethodType
                    MethodHandleDesc.ofMethod(DirectMethodHandleDesc.Kind.STATIC, CD_Maps,
                            "canonicalizeWithCaptured", MTD_mapsCanonicalizeWithCaptured),
                    MethodTypeDesc.of(CD_Map, CD_Map)));                       // instantiatedMethodType
            return;
        }
        Type element = switch (type) {
            case Type.ListOf t -> t.element();
            case Type.SetOf t -> t.element();
            case Type.OptionOf t -> t.element();
            default -> throw new IllegalArgumentException(
                    "canonicalizeAtCrossing does not compose a Function for " + type
                            + " as a container's element");
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
