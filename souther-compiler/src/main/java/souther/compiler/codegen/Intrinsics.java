package souther.compiler.codegen;

import souther.compiler.jvm.SoutherJvmAbi;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.Type;
import souther.compiler.core.Core;
import souther.compiler.core.Kernel;

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

    /** Emits {@code kernel}, leaving its result on the stack, and returns the result's Souther type
     * (spec §stdlib). Throws where this table has no row for it — the language names the kernel and
     * the JVM answers it, so a kernel with no answer here is this backend behind the library. */
    static Type emit(BodyGen g, Kernel kernel, Core.Call call) {
        Emit e = TABLE.get(kernel);
        if (e == null) {
            throw new IllegalStateException("the JVM emits nothing for `" + kernel.key() + "`");
        }
        return e.emit(g, kernel, call);
    }

    sealed interface Emit permits RuntimeStatic, JdkVirtual, NumericFold, TakesAFunction,
            DeclaredStatic {
        Type emit(BodyGen g, Kernel kernel, Core.Call call);
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
        public Type emit(BodyGen g, Kernel kernel, Core.Call call) {
            Stdlib.Signature declared = g.library().intrinsic(kernel).signature();
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
        public Type emit(BodyGen g, Kernel kernel, Core.Call call) {
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
        public Type emit(BodyGen g, Kernel kernel, Core.Call call) {
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
     * first {@code argOrder} entry is the receiver; the rest are stack arguments.
     *
     * <p>The values go over as they are. This is the one emitter that reaches a host method without
     * a runtime kernel in between, so it is the one that has to be told what it may be used for: a
     * JDK operation named here takes the Souther values at that position without conversion and
     * answers on all of them (ADR-0112). An argument that would have to be changed to fit — an
     * {@code Int} narrowed to an {@code int} — or an operation that refuses some of the values it
     * admits belongs on a kernel, which owns the conversion and the refusal.
     *
     * <p>This carried a {@code l2iArgs} set that narrowed a listed argument with {@code l2i}. It had
     * no entries, and what it offered was the raw narrowing issue #976 is about, in the one place a
     * later kernel taking a host {@code int} would reach for it.
     */
    record JdkVirtual(ClassDesc owner, String method, MethodTypeDesc desc, int[] argOrder,
                      Type result) implements Emit {
        public Type emit(BodyGen g, Kernel kernel, Core.Call call) {
            for (int src : argOrder) {
                g.genExpr(call.args().get(src));
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
        public Type emit(BodyGen g, Kernel kernel, Core.Call call) {
            Type result = call.type();
            if (result != Type.INT && result != Type.DECIMAL) {
                // the checker admits these two and nothing else; anything here is this compiler
                // disagreeing with itself, and emitting the Int kernel for it would answer a wrong
                // number rather than say so
                throw new IllegalStateException("`" + call.fn() + "` reached the backend answering " + Type.show(result)
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
                case TIME -> CD_LocalTime;
                case DATETIME -> CD_LocalDateTime;
                case INSTANT -> CD_Instant;
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
        // So is a declaration the language itself gives ({@code RoundingMode}): a kernel taking one
        // names its class, and what that class is called is the ABI's to say. Spelled from the
        // identity here, this was the one route from a Souther name to a JVM one that did not go
        // through `SoutherJvmAbi` — which is the place that exists to be the only one.
        if (t instanceof Type.Ref r && SoutherJvmAbi.providedByTheRuntime(r.name())) {
            return SoutherJvmAbi.nameOfLanguageDeclaration(r.name()).classDesc();
        }
        return CD_Object;   // Ref, Var, Tuple, Union, Nothing
    }

    // --- the registry ---

    private static final Map<Kernel, Emit> TABLE = buildTable();

    /** Every kernel this table emits. One here with no declaration naming it is a kernel the library
     *  ships and no signature describes, which is what {@code BUILTINS} used to be. */
    static Set<Kernel> kernels() {
        return TABLE.keySet();
    }

    /**
     * A kernel of the ordered family, over an element whose order lives on its sum: the runtime call
     * this table already holds for it, taking a comparator ahead of what it was already taking. The
     * comparator and the kernel's own arguments are on the stack, and {@code byArg} is their types
     * as they were emitted, in the order the kernel declares them.
     *
     * <p>Here rather than in the emitter that pushes the comparator, because which runtime method
     * answers a kernel and what it answers with are this table's to say. Written out there, the
     * class, the method and the result would each be stated a second time, and a row changed here
     * would leave the second statement behind.
     *
     * <p>Both row shapes that can take one. A kernel walking a container takes the container alone;
     * one applying a function takes the function too, as an {@code Fn}, and which argument the
     * container is is the row's answer rather than a position written out again.
     */
    static void emitWithComparator(BodyGen g, Kernel kernel, List<Type> byArg) {
        ClassDesc owner;
        String method;
        Type result;
        ClassDesc[] params;
        switch (TABLE.get(kernel)) {
            case RuntimeStatic row when row.result() != null && byArg.size() == 1 -> {
                owner = row.owner();
                method = row.method();
                result = row.result().apply(byArg);
                params = new ClassDesc[] {CD_Comparator, boundaryDesc(byArg.get(0))};
            }
            case TakesAFunction row when byArg.size() == 2 -> {
                owner = row.owner();
                method = row.method();
                result = row.result().apply(byArg);
                params = new ClassDesc[] {
                        CD_Comparator, CD_Fn, boundaryDesc(byArg.get(row.container()))};
            }
            case Emit row -> throw new IllegalStateException("`" + kernel.key() + "` is emitted as "
                    + row + ", which takes no comparator over " + byArg.size() + " argument(s)");
            case null -> throw new IllegalStateException(
                    "the JVM emits nothing for `" + kernel.key() + "`");
        }
        g.emitInvokeStatic(owner, method, MethodTypeDesc.of(boundaryDesc(result), params));
    }

    /** How each kernel is emitted — read by the test that holds the descriptor invariant. */
    static Map<Kernel, Emit> emitters() {
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
        return new JdkVirtual(owner, method, desc, argOrder, result);
    }

    private static MethodTypeDesc mtd(ClassDesc ret, ClassDesc... params) {
        return MethodTypeDesc.of(ret, params);
    }

    private static Map<Kernel, Emit> buildTable() {
        ClassDesc bool = ConstantDescs.CD_boolean;
        ClassDesc lng = ConstantDescs.CD_long;
        Map<Kernel, Emit> t = new java.util.EnumMap<>(Kernel.class);

        // String — JDK-native instance methods (explicit descriptor); receiver is the last Souther arg.
        t.put(Kernel.STRING_TO_INT, rtDeclared(CD_Strings, "toInt", order(0)));
        t.put(Kernel.STRING_TO_DECIMAL, rtDeclared(CD_Strings, "toDecimal", order(0)));
        t.put(Kernel.STRING_LENGTH, rt(CD_Strings, "length", order(0), ts -> Type.INT));
        t.put(Kernel.STRING_TRIM, jdk(CD_String, "trim", mtd(CD_String), order(0), Type.STRING));
        t.put(Kernel.STRING_LOWERCASE, jdk(CD_String, "toLowerCase", mtd(CD_String), order(0), Type.STRING));
        t.put(Kernel.STRING_UPPERCASE, jdk(CD_String, "toUpperCase", mtd(CD_String), order(0), Type.STRING));
        t.put(Kernel.STRING_CONTAINS, jdk(CD_String, "contains", mtd(bool, CD_CharSequence), order(1, 0), Type.BOOL));
        t.put(Kernel.STRING_STARTS_WITH, jdk(CD_String, "startsWith", mtd(bool, CD_String), order(1, 0), Type.BOOL));
        t.put(Kernel.STRING_ENDS_WITH, jdk(CD_String, "endsWith", mtd(bool, CD_String), order(1, 0), Type.BOOL));
        t.put(Kernel.STRING_APPEND, jdk(CD_String, "concat", mtd(CD_String, CD_String), order(0, 1), Type.STRING));
        // String — Strings runtime statics (descriptor derived).
        // `slice` left the JDK's `substring` when the language settled on code points: the JDK method
        // indexes UTF-16 units, so the conversion — and the abort for an index the string has not
        // got — lives in the runtime rather than in a descriptor here.
        t.put(Kernel.STRING_SLICE, rt(CD_Strings, "slice", order(2, 0, 1), ts -> Type.STRING));
        t.put(Kernel.STRING_SPLIT, rt(CD_Strings, "split", order(1, 0), ts -> Type.list(Type.STRING)));
        t.put(Kernel.STRING_JOIN, rt(CD_Strings, "join", order(1, 0), ts -> Type.STRING));
        t.put(Kernel.STRING_REPLACE, rt(CD_Strings, "replace", order(2, 0, 1), ts -> Type.STRING));
        t.put(Kernel.STRING_WORDS, rt(CD_Strings, "words", order(0), ts -> Type.list(Type.STRING)));
        t.put(Kernel.STRING_MATCHES, rt(CD_Strings, "matches", order(1, 0), ts -> Type.BOOL));
        t.put(Kernel.STRING_CHARACTERS, rt(CD_Strings, "characters", order(0), ts -> Type.list(Type.STRING)));
        t.put(Kernel.STRING_CODE_POINTS, rt(CD_Strings, "codePoints", order(0), ts -> Type.list(Type.INT)));
        t.put(Kernel.STRING_FROM_INT, rt(CD_Strings, "fromInt", order(0), ts -> Type.STRING));
        t.put(Kernel.STRING_CONCAT, rt(CD_Strings, "concat", order(0), ts -> Type.STRING));
        t.put(Kernel.STRING_REVERSE, rt(CD_Strings, "reverse", order(0), ts -> Type.STRING));
        t.put(Kernel.STRING_REPEAT, rt(CD_Strings, "repeat", order(1, 0), ts -> Type.STRING));
        t.put(Kernel.STRING_LINES, rt(CD_Strings, "lines", order(0), ts -> Type.list(Type.STRING)));
        t.put(Kernel.STRING_PAD_LEFT, rt(CD_Strings, "padLeft", order(2, 0, 1), ts -> Type.STRING));
        t.put(Kernel.STRING_PAD_RIGHT, rt(CD_Strings, "padRight", order(2, 0, 1), ts -> Type.STRING));
        t.put(Kernel.STRING_FROM_DECIMAL, rt(CD_Strings, "fromDecimal", order(0), ts -> Type.STRING));

        t.put(Kernel.DECIMAL_TO_INT, new DeclaredStatic(CD_DecimalMath, "toInt"));
        t.put(Kernel.DECIMAL_ROUND, new DeclaredStatic(CD_DecimalMath, "round"));

        // List
        t.put(Kernel.LIST_SORT_BY, new TakesAFunction(CD_Lists, "sortBy", 1,
                held -> List.of(((Type.ListOf) held).element()),
                ts -> ts.get(1)));
        t.put(Kernel.LIST_FIND, new TakesAFunction(CD_Lists, "find", 1,
                held -> List.of(((Type.ListOf) held).element()),
                ts -> Type.option(((Type.ListOf) ts.get(1)).element())));
        t.put(Kernel.OPTION_MAP, new TakesAFunction(CD_Options, "map", 1,
                held -> List.of(((Type.OptionOf) held).element()),
                ts -> Type.option(((Type.FnOf) ts.get(0)).result())));
        t.put(Kernel.LIST_MAX, rt(CD_Lists, "max", order(0), ts -> Type.option(listOf(ts, 0).element())));
        t.put(Kernel.LIST_MIN, rt(CD_Lists, "min", order(0), ts -> Type.option(listOf(ts, 0).element())));
        t.put(Kernel.LIST_LENGTH, rt(CD_Lists, "length", order(0), ts -> Type.INT));
        t.put(Kernel.LIST_GET, rt(CD_Lists, "get", order(1, 0), ts -> Type.option(listOf(ts, 1).element())));
        t.put(Kernel.LIST_SORT, rt(CD_Lists, "sort", order(0), ts -> ts.get(0)));
        t.put(Kernel.LIST_REVERSE, rt(CD_Lists, "reverse", order(0), ts -> ts.get(0)));
        t.put(Kernel.LIST_RANGE_INCLUSIVE, rt(CD_Lists, "rangeInclusive", order(0, 1), ts -> Type.list(Type.INT)));
        t.put(Kernel.LIST_SUM, new NumericFold("sumInt", "sumDecimal"));
        t.put(Kernel.LIST_PRODUCT, new NumericFold("productInt", "productDecimal"));

        // Map — keys/values are erased to Object; the map argument stays a raw Map.
        t.put(Kernel.MAP_GET, rtErased(CD_Maps, "get", order(1, 0), Set.of(0),
                ts -> Type.option(mapOf(ts, 1).value())));
        t.put(Kernel.MAP_EMPTY, rt(CD_Maps, "empty", order(), ts -> Type.map(Type.NOTHING, Type.NOTHING)));
        t.put(Kernel.MAP_CONTAINS_KEY, rtErased(CD_Maps, "containsKey", order(1, 0), Set.of(0), ts -> Type.BOOL));
        t.put(Kernel.MAP_KEYS, rt(CD_Maps, "keys", order(0), ts -> Type.list(mapOf(ts, 0).key())));
        t.put(Kernel.MAP_VALUES, rt(CD_Maps, "values", order(0), ts -> Type.list(mapOf(ts, 0).value())));
        t.put(Kernel.MAP_SINGLETON, rtErased(CD_Maps, "singleton", order(0, 1), Set.of(0, 1),
                ts -> Type.map(ts.get(0), ts.get(1))));
        t.put(Kernel.MAP_INSERT, rtErased(CD_Maps, "insert", order(0, 1, 2), Set.of(0, 1),
                Intrinsics::mapInsertResult));
        t.put(Kernel.MAP_REMOVE, rtErased(CD_Maps, "remove", order(0, 1), Set.of(0), ts -> ts.get(1)));
        t.put(Kernel.MAP_IS_EMPTY, rt(CD_Maps, "isEmpty", order(0), ts -> Type.BOOL));
        t.put(Kernel.MAP_SIZE, rt(CD_Maps, "size", order(0), ts -> Type.INT));
        t.put(Kernel.MAP_TO_LIST, rt(CD_Maps, "toList", order(0), ts -> {
            Type.MapOf m = mapOf(ts, 0);
            return Type.list(Type.tuple(List.of(m.key(), m.value())));
        }));
        t.put(Kernel.MAP_FROM_LIST, rt(CD_Maps, "fromList", order(0), Intrinsics::mapFromListResult));

        // Set — the element is erased to Object; a set argument stays a raw Set.
        t.put(Kernel.SET_EMPTY, rt(CD_Sets, "empty", order(), ts -> Type.set(Type.NOTHING)));
        t.put(Kernel.SET_SINGLETON, rtErased(CD_Sets, "singleton", order(0), Set.of(0), ts -> Type.set(ts.get(0))));
        t.put(Kernel.SET_INSERT, rtErased(CD_Sets, "insert", order(0, 1), Set.of(0), Intrinsics::setInsertResult));
        t.put(Kernel.SET_REMOVE, rtErased(CD_Sets, "remove", order(0, 1), Set.of(0), ts -> ts.get(1)));
        t.put(Kernel.SET_CONTAINS, rtErased(CD_Sets, "contains", order(0, 1), Set.of(0), ts -> Type.BOOL));
        t.put(Kernel.SET_UNION, rt(CD_Sets, "union", order(0, 1), ts -> setUnionType(ts.get(0), ts.get(1))));
        t.put(Kernel.SET_INTERSECTION, rt(CD_Sets, "intersection", order(0, 1), ts -> ts.get(0)));
        t.put(Kernel.SET_DIFFERENCE, rt(CD_Sets, "difference", order(0, 1), ts -> ts.get(0)));
        t.put(Kernel.SET_IS_EMPTY, rt(CD_Sets, "isEmpty", order(0), ts -> Type.BOOL));
        t.put(Kernel.SET_SIZE, rt(CD_Sets, "size", order(0), ts -> Type.INT));
        t.put(Kernel.SET_TO_LIST, rt(CD_Sets, "toList", order(0), ts -> Type.list(setOf(ts, 0).element())));
        t.put(Kernel.SET_FROM_LIST, rt(CD_Sets, "fromList", order(0), ts -> Type.set(listOf(ts, 0).element())));

        // Date / DateTime — the temporal is the receiver (emitted first); the count is a long.
        // Through the runtime rather than straight to `java.time`: a shift off the end of the range
        // aborts saying what it was doing, instead of the JVM's own exception reaching the boundary
        // and naming a class the language has no type for.
        t.put(Kernel.DATE_ADD_DAYS, rt(CD_Temporals, "addDays", order(1, 0), ts -> Type.DATE));
        t.put(Kernel.DATE_ADD_MONTHS, rt(CD_Temporals, "addMonths", order(1, 0), ts -> Type.DATE));
        t.put(Kernel.DATE_ADD_YEARS, rt(CD_Temporals, "addYears", order(1, 0), ts -> Type.DATE));
        t.put(Kernel.DATE_DAYS_BETWEEN, rt(CD_Temporals, "daysBetween", order(0, 1), ts -> Type.INT));
        t.put(Kernel.DATE_YEAR, rt(CD_Temporals, "year", order(0), ts -> Type.INT));
        t.put(Kernel.DATE_MONTH, rt(CD_Temporals, "month", order(0), ts -> Type.INT));
        t.put(Kernel.DATE_DAY, rt(CD_Temporals, "day", order(0), ts -> Type.INT));
        // Building from parts: partial, so the declaration states `Date | NotADate` and the emitter
        // takes the result from it rather than working one out.
        t.put(Kernel.DATE_FROM_PARTS, rtDeclared(CD_Temporals, "fromDateParts", order(0, 1, 2)));
        t.put(Kernel.TIME_FROM_PARTS, rtDeclared(CD_Temporals, "fromTimeParts", order(0, 1, 2)));
        t.put(Kernel.TIME_HOUR, rt(CD_Temporals, "hour", order(0), ts -> Type.INT));
        t.put(Kernel.TIME_MINUTE, rt(CD_Temporals, "minute", order(0), ts -> Type.INT));
        t.put(Kernel.TIME_SECOND, rt(CD_Temporals, "second", order(0), ts -> Type.INT));
        t.put(Kernel.DATETIME_ADD_MINUTES, rt(CD_Temporals, "addMinutes", order(1, 0), ts -> Type.DATETIME));
        t.put(Kernel.DATETIME_ADD_HOURS, rt(CD_Temporals, "addHours", order(1, 0), ts -> Type.DATETIME));
        // `addDateTimeDays` rather than a second `addDays`: the runtime is Java, which would take the
        // two as overloads and leave the emitter's descriptor deciding which, where the kernel already
        // says which temporal it is for.
        t.put(Kernel.DATETIME_ADD_DAYS, rt(CD_Temporals, "addDateTimeDays", order(1, 0), ts -> Type.DATETIME));
        t.put(Kernel.DATETIME_MINUTES_BETWEEN, rt(CD_Temporals, "minutesBetween", order(0, 1), ts -> Type.INT));
        t.put(Kernel.DATETIME_TO_DATE,
                jdk(CD_LocalDateTime, "toLocalDate", mtd(CD_LocalDate), order(0), Type.DATE));
        t.put(Kernel.DATETIME_TO_TIME,
                jdk(CD_LocalDateTime, "toLocalTime", mtd(CD_LocalTime), order(0), Type.TIME));
        // A date and a time of day are both settled values, so joining them cannot fail: total, with
        // the date as the receiver of `LocalDate.atTime`.
        t.put(Kernel.DATETIME_FROM_DATE_AND_TIME,
                jdk(CD_LocalDate, "atTime", mtd(CD_LocalDateTime, CD_LocalTime), order(0, 1), Type.DATETIME));

        // Int — IntMath statics. add/subtract/multiply share the overflow-aborting kernel with the
        // `+ - *` operators; modBy aborts on a zero divisor; compare returns -1/0/1.
        t.put(Kernel.INT_ADD, rt(CD_IntMath, "addExact", order(0, 1), ts -> Type.INT));
        t.put(Kernel.INT_SUBTRACT, rt(CD_IntMath, "subtractExact", order(0, 1), ts -> Type.INT));
        t.put(Kernel.INT_MULTIPLY, rt(CD_IntMath, "multiplyExact", order(0, 1), ts -> Type.INT));
        t.put(Kernel.INT_COMPARE, rt(CD_IntMath, "compare", order(0, 1), ts -> Type.INT));
        t.put(Kernel.INT_FLOOR_MOD, rt(CD_IntMath, "floorMod", order(0, 1), ts -> Type.INT));

        // Decimal — every one of them a DecimalMath static, read off its declaration. What a
        // BigDecimal method does is not what a Souther operation means: each of these is partial at
        // the ends of the scale range, and the abort that reports it belongs to the operation rather
        // than to whoever emitted the call (ADR-0112). One emitter for the whole module, so a
        // Decimal operation added later has one place to be written and no second shape to pick.
        t.put(Kernel.DECIMAL_ADD, new DeclaredStatic(CD_DecimalMath, "add"));
        t.put(Kernel.DECIMAL_SUBTRACT, new DeclaredStatic(CD_DecimalMath, "subtract"));
        t.put(Kernel.DECIMAL_MULTIPLY, new DeclaredStatic(CD_DecimalMath, "multiply"));
        t.put(Kernel.DECIMAL_DIVIDE, new DeclaredStatic(CD_DecimalMath, "divide"));
        t.put(Kernel.DECIMAL_COMPARE, new DeclaredStatic(CD_DecimalMath, "compare"));
        t.put(Kernel.DECIMAL_FROM_INT, new DeclaredStatic(CD_DecimalMath, "fromInt"));

        // Not a copy: the map is a local nothing else holds, and read back through an EnumMap it
        // answers in the order the kernels are declared in rather than in whatever order a copy
        // happens to hash them into.
        return java.util.Collections.unmodifiableMap(t);
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
