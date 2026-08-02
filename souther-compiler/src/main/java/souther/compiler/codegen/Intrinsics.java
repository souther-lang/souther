package souther.compiler.codegen;

import souther.compiler.Prelude;
import souther.compiler.diag.CompileException;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;
import souther.compiler.core.Core;

import java.lang.constant.ClassDesc;
import java.lang.constant.ConstantDescs;
import java.lang.constant.MethodTypeDesc;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

import static souther.compiler.codegen.Descriptors.*;

/**
 * The data-driven registry mapping each stdlib intrinsic key to its bytecode emission.
 *
 * <p>A runtime-backed primitive (a call to {@code Maps}/{@code Sets}/{@code Strings}/{@code Lists}/
 * {@code Temporals}) is emitted from one table row: the row names the runtime class, method, the
 * argument order (Souther puts the subject last for pipe reading; the runtime method takes it in a
 * fixed position, so the row carries the permutation), the argument slots the runtime method erases
 * to {@code Object} (map keys/values, set elements), and how to type the result. The JVM descriptor
 * is <em>derived</em> from the observed argument types and the result type — it is not restated, so
 * adding an intrinsic is a {@code .sou} signature, a runtime method, and one row here.
 *
 * <p>The JDK-native calls ({@code String} instance methods, {@code java.time} {@code plus*}) keep an
 * explicit descriptor because JDK signatures use {@code CharSequence}/{@code int}, which the boundary
 * derivation does not model. That set is stable — the JDK method surface does not grow with the
 * standard library.
 */
final class Intrinsics {

    private Intrinsics() {
    }

    /** Emits the intrinsic named by {@code key}, leaving its result on the stack, and returns the
     * result's Souther type (spec §stdlib). Throws on an unknown key — the checker admits only keys
     * that were declared {@code = intrinsic "..."} in a prelude module, so this is a compiler bug. */
    static Type emit(BodyGen g, String key, Core.Call call) {
        Emit e = TABLE.get(key);
        if (e == null) {
            throw new CompileException(call.pos(), "unknown intrinsic `" + key + "`");
        }
        return e.emit(g, key, call);
    }

    sealed interface Emit permits RuntimeStatic, JdkVirtual, NumericFold, TakesAFunction,
            DeclaredStatic {
        Type emit(BodyGen g, String key, Core.Call call);
    }

    /**
     * An {@code invokestatic} whose descriptor comes from the kernel's core declaration: each
     * parameter is the boundary form of the declared parameter type, the return the boundary form
     * of the declared result. A descriptor belongs to the callee — deriving one from the observed
     * argument types only ever agreed with it while every parameter type was invariant, and a
     * sum-typed parameter ({@code RoundingMode}) ends that: the argument's type may be the case it
     * happens to be, while the declaration names the sum.
     */
    record DeclaredStatic(ClassDesc owner, String method) implements Emit {
        public Type emit(BodyGen g, String key, Core.Call call) {
            Prelude.Signature declared = Prelude.kernelSignature(key);
            ClassDesc[] params = new ClassDesc[declared.params().size()];
            for (int i = 0; i < params.length; i++) {
                params[i] = boundaryDesc(declared.params().get(i));
            }
            for (Core arg : call.args()) {
                g.genExpr(arg);
            }
            g.emitInvokeStatic(owner, method,
                    MethodTypeDesc.of(boundaryDesc(declared.result()), params));
            return declared.result();
        }
    }

    /**
     * A kernel taking a function value. The function is not inlined into the call — the kernel is
     * what applies it — so it is materialised as an {@code Fn}, at the parameter types the container
     * it walks supplies.
     *
     * <p>{@code container} is which argument that container is; {@code paramTypes} reads the
     * function's parameter types off it. The function goes first on the stack, as the declarations
     * write it.
     */
    record TakesAFunction(ClassDesc owner, String method, int container,
                          Function<Type, List<Type>> paramTypes,
                          Function<List<Type>, Type> result) implements Emit {
        public Type emit(BodyGen g, String key, Core.Call call) {
            Type held = call.args().get(container).type();
            g.emitFn(call.args().get(0), paramTypes.apply(held));
            g.genExpr(call.args().get(container));
            List<Type> byArg = List.of(call.args().get(0).type(), held);
            Type resultType = result.apply(byArg);
            g.emitInvokeStatic(owner, method, MethodTypeDesc.of(boundaryDesc(resultType),
                    CD_Fn, boundaryDesc(held)));
            return resultType;
        }
    }

    /**
     * An {@code invokestatic} to a Souther runtime class. The descriptor is derived: each parameter is
     * {@code Object} when its argument occupies an erased slot ({@code objectSlots}), otherwise the
     * boundary form of the observed argument type; the return is the boundary form of the result type.
     * Arguments are emitted in {@code argOrder} (a permutation over all arguments); an erased slot is
     * boxed, which is a no-op for a reference.
     */
    record RuntimeStatic(ClassDesc owner, String method, int[] argOrder,
                         Set<Integer> objectSlots, Function<List<Type>, Type> result) implements Emit {
        public Type emit(BodyGen g, String key, Core.Call call) {
            int n = argOrder.length;
            Type[] byArg = new Type[n];
            ClassDesc[] params = new ClassDesc[n];
            for (int j = 0; j < n; j++) {
                int src = argOrder[j];
                Type t = g.genExpr(call.args().get(src));
                boolean erased = objectSlots.contains(src);
                if (erased) {
                    g.emitBox(t);
                }
                byArg[src] = t;
                params[j] = erased ? CD_Object : boundaryDesc(t);
            }
            Type resultType = result == null ? call.type() : result.apply(List.of(byArg));
            g.emitInvokeStatic(owner, method, MethodTypeDesc.of(boundaryDesc(resultType), params));
            return resultType;
        }
    }

    /**
     * An {@code invokevirtual} to a JDK / {@code java.time} class with an explicit descriptor. The
     * first {@code argOrder} entry is the receiver; the rest are stack arguments. An argument listed in
     * {@code l2iArgs} is narrowed from Souther's {@code Int} (a {@code long}) to a JVM {@code int}.
     */
    record JdkVirtual(ClassDesc owner, String method, MethodTypeDesc desc, int[] argOrder,
                      Set<Integer> l2iArgs, Type result) implements Emit {
        public Type emit(BodyGen g, String key, Core.Call call) {
            for (int src : argOrder) {
                g.genExpr(call.args().get(src));
                if (l2iArgs.contains(src)) {
                    g.emitL2i();
                }
            }
            g.emitInvokeVirtual(owner, method, desc);
            return result;
        }
    }

    /**
     * {@code List.sum} / {@code List.product}. The two numeric elements run different kernels and
     * answer different JVM types (a {@code long}, a {@code BigDecimal}), so the method is read off
     * the result the checker settled rather than named in the row. The list argument alone cannot
     * say which: over the empty-list literal its element is the bottom, and the answer came from the
     * position the call was written in.
     */
    record NumericFold(String intMethod, String decimalMethod) implements Emit {
        public Type emit(BodyGen g, String key, Core.Call call) {
            Type result = call.type();
            if (result != Type.INT && result != Type.DECIMAL) {
                // the checker admits these two and nothing else; anything here is this compiler
                // disagreeing with itself, and emitting the Int kernel for it would answer a wrong
                // number rather than say so
                throw new CompileException(call.pos(),
                        "`" + call.fn() + "` reached the backend answering " + Type.show(result)
                                + ", which is neither Int nor Decimal");
            }
            g.genExpr(call.args().get(0));
            String method = result == Type.DECIMAL ? decimalMethod : intMethod;
            g.emitInvokeStatic(CD_Lists, method, MethodTypeDesc.of(boundaryDesc(result), CD_List));
            return result;
        }
    }

    /** The JVM type a value takes at a runtime-method boundary: primitives unboxed, containers as
     * their raw interface, everything else (references, type variables, tuples) as {@code Object}. */
    private static ClassDesc boundaryDesc(Type t) {
        if (t instanceof Type.Prim p) {
            return switch (p) {
                case INT -> ConstantDescs.CD_long;
                case BOOL -> ConstantDescs.CD_boolean;
                case DECIMAL -> CD_BigDecimal;
                case STRING -> CD_String;
                case DATE -> CD_LocalDate;
                case DATETIME -> CD_LocalDateTime;
                case RAW -> CD_Object;
            };
        }
        if (t instanceof Type.ListOf) {
            return CD_List;
        }
        if (t instanceof Type.MapOf) {
            return CD_Map;
        }
        if (t instanceof Type.SetOf) {
            return CD_Set;
        }
        // An optional is a runtime class of its own, not an erased reference: a kernel answering one
        // declares it, so the descriptor has to name it or the call finds no such method.
        if (t instanceof Type.OptionOf) {
            return CD_Option;
        }
        // So is a name of the runtime namespace ({@code RoundingMode}): it is the real package of
        // the classes souther-runtime ships (see TypeName.RUNTIME), so a kernel taking one names it.
        if (t instanceof Type.Ref r && TypeName.RUNTIME.equals(r.name().module())) {
            return ClassDesc.of(r.name().qualified());
        }
        return CD_Object;   // Ref, Var, Tuple, Union, Nothing
    }

    // --- the registry ---

    private static final Map<String, Emit> TABLE = buildTable();

    /** Every kernel key this table emits. A key here with no declaration naming it is a kernel the
     *  library ships and no signature describes, which is what {@code BUILTINS} used to be. */
    static Set<String> keys() {
        return TABLE.keySet();
    }

    /** How each key is emitted — read by the test that holds the descriptor invariant. */
    static Map<String, Emit> emitters() {
        return Map.copyOf(TABLE);
    }

    private static int[] order(int... a) {
        return a;
    }

    private static Emit rt(ClassDesc owner, String method, int[] argOrder, Function<List<Type>, Type> result) {
        return new RuntimeStatic(owner, method, argOrder, Set.of(), result);
    }

    /** The same, for a kernel whose result the declaration already states outright — nothing about
     *  the arguments narrows it, so the type the checker settled is the answer rather than one this
     *  table works out again. */
    private static Emit rtDeclared(ClassDesc owner, String method, int[] argOrder) {
        return new RuntimeStatic(owner, method, argOrder, Set.of(), null);
    }

    private static Emit rtErased(ClassDesc owner, String method, int[] argOrder, Set<Integer> objectSlots,
                                 Function<List<Type>, Type> result) {
        return new RuntimeStatic(owner, method, argOrder, objectSlots, result);
    }

    private static Emit jdk(ClassDesc owner, String method, MethodTypeDesc desc, int[] argOrder, Type result) {
        return new JdkVirtual(owner, method, desc, argOrder, Set.of(), result);
    }

    private static MethodTypeDesc mtd(ClassDesc ret, ClassDesc... params) {
        return MethodTypeDesc.of(ret, params);
    }

    private static Map<String, Emit> buildTable() {
        ClassDesc bool = ConstantDescs.CD_boolean;
        ClassDesc lng = ConstantDescs.CD_long;
        ClassDesc intCd = ConstantDescs.CD_int;
        Map<String, Emit> t = new java.util.LinkedHashMap<>();

        // String — JDK-native instance methods (explicit descriptor); receiver is the last Souther arg.
        t.put("string.toInt", rtDeclared(CD_Strings, "toInt", order(0)));
        t.put("string.toDecimal", rtDeclared(CD_Strings, "toDecimal", order(0)));
        t.put("string.length", rt(CD_Strings, "length", order(0), ts -> Type.INT));
        t.put("string.trim", jdk(CD_String, "trim", mtd(CD_String), order(0), Type.STRING));
        t.put("string.lowercase", jdk(CD_String, "toLowerCase", mtd(CD_String), order(0), Type.STRING));
        t.put("string.uppercase", jdk(CD_String, "toUpperCase", mtd(CD_String), order(0), Type.STRING));
        t.put("string.contains", jdk(CD_String, "contains", mtd(bool, CD_CharSequence), order(1, 0), Type.BOOL));
        t.put("string.startsWith", jdk(CD_String, "startsWith", mtd(bool, CD_String), order(1, 0), Type.BOOL));
        t.put("string.endsWith", jdk(CD_String, "endsWith", mtd(bool, CD_String), order(1, 0), Type.BOOL));
        t.put("string.substring", new JdkVirtual(CD_String, "substring", mtd(CD_String, intCd, intCd),
                order(2, 0, 1), Set.of(0, 1), Type.STRING));
        t.put("string.append", jdk(CD_String, "concat", mtd(CD_String, CD_String), order(0, 1), Type.STRING));
        // String — Strings runtime statics (descriptor derived).
        t.put("string.split", rt(CD_Strings, "split", order(1, 0), ts -> Type.list(Type.STRING)));
        t.put("string.join", rt(CD_Strings, "join", order(1, 0), ts -> Type.STRING));
        t.put("string.replace", rt(CD_Strings, "replace", order(2, 0, 1), ts -> Type.STRING));
        t.put("string.words", rt(CD_Strings, "words", order(0), ts -> Type.list(Type.STRING)));
        t.put("string.matches", rt(CD_Strings, "matches", order(1, 0), ts -> Type.BOOL));
        t.put("string.toChars", rt(CD_Strings, "toChars", order(0), ts -> Type.list(Type.STRING)));
        t.put("string.toCode", rt(CD_Strings, "toCode", order(0), ts -> Type.INT));
        t.put("string.fromInt", rt(CD_Strings, "fromInt", order(0), ts -> Type.STRING));
        t.put("string.concat", rt(CD_Strings, "concat", order(0), ts -> Type.STRING));
        t.put("string.reverse", rt(CD_Strings, "reverse", order(0), ts -> Type.STRING));
        t.put("string.repeat", rt(CD_Strings, "repeat", order(1, 0), ts -> Type.STRING));
        t.put("string.lines", rt(CD_Strings, "lines", order(0), ts -> Type.list(Type.STRING)));
        t.put("string.padLeft", rt(CD_Strings, "padLeft", order(2, 0, 1), ts -> Type.STRING));
        t.put("string.padRight", rt(CD_Strings, "padRight", order(2, 0, 1), ts -> Type.STRING));
        t.put("string.fromDecimal", rt(CD_Strings, "fromDecimal", order(0), ts -> Type.STRING));

        t.put("decimal.toInt", new DeclaredStatic(CD_DecimalMath, "toInt"));
        t.put("decimal.round", new DeclaredStatic(CD_DecimalMath, "round"));

        // List
        t.put("list.sortBy", new TakesAFunction(CD_Lists, "sortBy", 1,
                held -> List.of(((Type.ListOf) held).element()),
                ts -> ts.get(1)));
        t.put("list.find", new TakesAFunction(CD_Lists, "find", 1,
                held -> List.of(((Type.ListOf) held).element()),
                ts -> Type.option(((Type.ListOf) ts.get(1)).element())));
        t.put("option.map", new TakesAFunction(CD_Options, "map", 1,
                held -> List.of(((Type.OptionOf) held).element()),
                ts -> Type.option(((Type.FnOf) ts.get(0)).result())));
        t.put("list.max", rt(CD_Lists, "max", order(0), ts -> Type.option(listOf(ts, 0).element())));
        t.put("list.min", rt(CD_Lists, "min", order(0), ts -> Type.option(listOf(ts, 0).element())));
        t.put("list.length", rt(CD_Lists, "length", order(0), ts -> Type.INT));
        t.put("list.get", rt(CD_Lists, "get", order(1, 0), ts -> Type.option(listOf(ts, 1).element())));
        t.put("list.sort", rt(CD_Lists, "sort", order(0), ts -> ts.get(0)));
        t.put("list.reverse", rt(CD_Lists, "reverse", order(0), ts -> ts.get(0)));
        t.put("list.range", rt(CD_Lists, "range", order(0, 1), ts -> Type.list(Type.INT)));
        t.put("list.sum", new NumericFold("sumInt", "sumDecimal"));
        t.put("list.product", new NumericFold("productInt", "productDecimal"));

        // Map — keys/values are erased to Object; the map argument stays a raw Map.
        t.put("map.get", rtErased(CD_Maps, "get", order(1, 0), Set.of(0),
                ts -> Type.option(mapOf(ts, 1).value())));
        t.put("map.empty", rt(CD_Maps, "empty", order(), ts -> Type.map(Type.NOTHING, Type.NOTHING)));
        t.put("map.containsKey", rtErased(CD_Maps, "containsKey", order(1, 0), Set.of(0), ts -> Type.BOOL));
        t.put("map.keys", rt(CD_Maps, "keys", order(0), ts -> Type.list(mapOf(ts, 0).key())));
        t.put("map.values", rt(CD_Maps, "values", order(0), ts -> Type.list(mapOf(ts, 0).value())));
        t.put("map.singleton", rtErased(CD_Maps, "singleton", order(0, 1), Set.of(0, 1),
                ts -> Type.map(ts.get(0), ts.get(1))));
        t.put("map.insert", rtErased(CD_Maps, "insert", order(0, 1, 2), Set.of(0, 1),
                Intrinsics::mapInsertResult));
        t.put("map.remove", rtErased(CD_Maps, "remove", order(0, 1), Set.of(0), ts -> ts.get(1)));
        t.put("map.isEmpty", rt(CD_Maps, "isEmpty", order(0), ts -> Type.BOOL));
        t.put("map.size", rt(CD_Maps, "size", order(0), ts -> Type.INT));
        t.put("map.toList", rt(CD_Maps, "toList", order(0), ts -> {
            Type.MapOf m = mapOf(ts, 0);
            return Type.list(Type.tuple(List.of(m.key(), m.value())));
        }));
        t.put("map.fromList", rt(CD_Maps, "fromList", order(0), Intrinsics::mapFromListResult));

        // Set — the element is erased to Object; a set argument stays a raw Set.
        t.put("set.empty", rt(CD_Sets, "empty", order(), ts -> Type.set(Type.NOTHING)));
        t.put("set.singleton", rtErased(CD_Sets, "singleton", order(0), Set.of(0), ts -> Type.set(ts.get(0))));
        t.put("set.insert", rtErased(CD_Sets, "insert", order(0, 1), Set.of(0), Intrinsics::setInsertResult));
        t.put("set.remove", rtErased(CD_Sets, "remove", order(0, 1), Set.of(0), ts -> ts.get(1)));
        t.put("set.contains", rtErased(CD_Sets, "contains", order(0, 1), Set.of(0), ts -> Type.BOOL));
        t.put("set.union", rt(CD_Sets, "union", order(0, 1), ts -> setUnionType(ts.get(0), ts.get(1))));
        t.put("set.intersect", rt(CD_Sets, "intersect", order(0, 1), ts -> ts.get(0)));
        t.put("set.difference", rt(CD_Sets, "difference", order(0, 1), ts -> ts.get(0)));
        t.put("set.isEmpty", rt(CD_Sets, "isEmpty", order(0), ts -> Type.BOOL));
        t.put("set.size", rt(CD_Sets, "size", order(0), ts -> Type.INT));
        t.put("set.toList", rt(CD_Sets, "toList", order(0), ts -> Type.list(setOf(ts, 0).element())));
        t.put("set.fromList", rt(CD_Sets, "fromList", order(0), ts -> Type.set(listOf(ts, 0).element())));

        // Date / DateTime — the temporal is the receiver (emitted first); the count is a long.
        t.put("date.addDays", jdk(CD_LocalDate, "plusDays", mtd(CD_LocalDate, lng), order(1, 0), Type.DATE));
        t.put("date.addMonths", jdk(CD_LocalDate, "plusMonths", mtd(CD_LocalDate, lng), order(1, 0), Type.DATE));
        t.put("date.addYears", jdk(CD_LocalDate, "plusYears", mtd(CD_LocalDate, lng), order(1, 0), Type.DATE));
        t.put("date.daysBetween", rt(CD_Temporals, "daysBetween", order(0, 1), ts -> Type.INT));
        t.put("date.year", rt(CD_Temporals, "year", order(0), ts -> Type.INT));
        t.put("date.month", rt(CD_Temporals, "month", order(0), ts -> Type.INT));
        t.put("date.day", rt(CD_Temporals, "day", order(0), ts -> Type.INT));
        t.put("datetime.addMinutes",
                jdk(CD_LocalDateTime, "plusMinutes", mtd(CD_LocalDateTime, lng), order(1, 0), Type.DATETIME));
        t.put("datetime.addHours",
                jdk(CD_LocalDateTime, "plusHours", mtd(CD_LocalDateTime, lng), order(1, 0), Type.DATETIME));
        t.put("datetime.addDays",
                jdk(CD_LocalDateTime, "plusDays", mtd(CD_LocalDateTime, lng), order(1, 0), Type.DATETIME));
        t.put("datetime.minutesBetween", rt(CD_Temporals, "minutesBetween", order(0, 1), ts -> Type.INT));
        t.put("datetime.toDate",
                jdk(CD_LocalDateTime, "toLocalDate", mtd(CD_LocalDate), order(0), Type.DATE));

        // Int — IntMath statics. add/subtract/multiply share the overflow-aborting kernel with the
        // `+ - *` operators; modBy aborts on a zero divisor; compare returns -1/0/1.
        t.put("int.add", rt(CD_IntMath, "addExact", order(0, 1), ts -> Type.INT));
        t.put("int.subtract", rt(CD_IntMath, "subtractExact", order(0, 1), ts -> Type.INT));
        t.put("int.multiply", rt(CD_IntMath, "multiplyExact", order(0, 1), ts -> Type.INT));
        t.put("int.compare", rt(CD_IntMath, "compare", order(0, 1), ts -> Type.INT));
        t.put("int.modBy", rt(CD_IntMath, "modBy", order(0, 1), ts -> Type.INT));

        // Decimal — add/subtract/multiply are BigDecimal instance methods (receiver is the first arg);
        // compare is a DecimalMath static returning -1/0/1.
        t.put("decimal.add", jdk(CD_BigDecimal, "add", MTD_bdArith, order(0, 1), Type.DECIMAL));
        t.put("decimal.subtract", jdk(CD_BigDecimal, "subtract", MTD_bdArith, order(0, 1), Type.DECIMAL));
        t.put("decimal.multiply", jdk(CD_BigDecimal, "multiply", MTD_bdArith, order(0, 1), Type.DECIMAL));
        t.put("decimal.compare", rt(CD_DecimalMath, "compare", order(0, 1), ts -> Type.INT));
        t.put("decimal.fromInt", rt(CD_DecimalMath, "fromInt", order(0), ts -> Type.DECIMAL));

        return Map.copyOf(t);
    }

    // --- result-type formulas for the intrinsics whose result is learned from argument types ---

    private static Type.MapOf mapOf(List<Type> ts, int i) {
        return (Type.MapOf) ts.get(i);
    }

    private static Type.SetOf setOf(List<Type> ts, int i) {
        return (Type.SetOf) ts.get(i);
    }

    private static Type.ListOf listOf(List<Type> ts, int i) {
        return (Type.ListOf) ts.get(i);
    }

    /** {@code insert(k, v, m)} keeps the map's element types, filling either side from the inserted
     * key/value when the map is the empty-map bottom (a fresh {@code Map.empty}). */
    private static Type mapInsertResult(List<Type> ts) {
        Type kt = ts.get(0);
        Type vt = ts.get(1);
        Type.MapOf m = mapOf(ts, 2);
        Type ek = m.key();
        Type ev = m.value();
        return Type.map(ek instanceof Type.Nothing ? kt : ek, ev instanceof Type.Nothing ? vt : ev);
    }

    /** {@code fromList(entries)} reads the (key, value) types off the list's tuple element. */
    private static Type mapFromListResult(List<Type> ts) {
        Type elem = listOf(ts, 0).element();
        if (elem instanceof Type.TupleOf tp) {
            return Type.map(tp.elements().get(0), tp.elements().get(1));
        }
        return Type.map(Type.NOTHING, Type.NOTHING);
    }

    /** {@code insert(e, s)} keeps the set's element type, filling it from the inserted element when
     * the set is the empty-set bottom. */
    private static Type setInsertResult(List<Type> ts) {
        Type vt = ts.get(0);
        Type existing = setOf(ts, 1).element();
        return Type.set(existing instanceof Type.Nothing ? vt : existing);
    }

    /** The element type of a set union: the concrete side when the other is the empty-set bottom,
     * else the left (the checker has already required the two to agree). */
    private static Type setUnionType(Type a, Type b) {
        Type ae = ((Type.SetOf) a).element();
        Type be = ((Type.SetOf) b).element();
        return Type.set(ae instanceof Type.Nothing ? be : ae);
    }
}
