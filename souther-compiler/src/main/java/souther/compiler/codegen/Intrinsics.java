package souther.compiler.codegen;

import souther.compiler.jvm.SoutherJvmAbi;
import souther.compiler.types.Type;
import souther.compiler.core.Core;
import souther.compiler.core.Kernel;
import souther.compiler.core.KernelSignature;

import java.lang.constant.ClassDesc;
import java.lang.constant.ConstantDescs;
import java.lang.constant.MethodTypeDesc;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

import static souther.compiler.codegen.Descriptors.*;

/**
 * What the JVM emits for each kernel this table backs.
 *
 * <p>Not every kernel of the language. {@code Int}'s partial division and its truncating remainder
 * are a branch and not a call, and {@code BodyGen} writes them out itself; which kernels are here
 * and which are there is held apart by {@code EveryKernelIsEmittedInOnePlaceTest} rather than
 * counted in a sentence.
 *
 * <p>One rule for what a call to a kernel here is emitted at: the descriptor comes from the
 * kernel's declaration, parameter by parameter and the result, through {@link #slotsOf}.
 *
 * <pre>{@code
 *   KernelSignature -> slotsOf -> descriptorOf
 * }</pre>
 *
 * <p>The declaration belongs to the callee, and a descriptor built from the types observed at a call
 * agrees with it only while no value can arrive narrower than the parameter it goes into. A
 * sum-typed parameter ends that, so nothing here reads the call for the shape of what it is calling.
 *
 * <p>What a row carries is what the declaration cannot say: which runtime class and method answer
 * the kernel, and the order that method takes the arguments in — Souther puts the subject last for
 * pipe reading, and the runtime method takes it where it takes it. So a kernel answered by a Souther
 * runtime static is a {@code .sou} declaration, a runtime method, and one row here.
 *
 * <p>Three things stand beside that rule, and only one of them sets it aside.
 *
 * <p>{@link #emitWithComparator} adds to it. The ordered family reaches a runtime method taking a
 * comparator the declaration does not name, so the derived descriptor is what the comparator is put
 * in front of — the base form and a delta, not a second derivation.
 *
 * <p>{@link NumericFold} keeps the descriptor and chooses the method. Such a kernel is declared over
 * any number and the runtime answers it with an implementation per representation, so the type the
 * checker settled picks which — an instantiation choosing between two implementations of one
 * operation, and the only thing a call-site type decides here.
 *
 * <p>{@link JdkVirtual} is the one that does not derive. It calls a JDK method, whose descriptor is
 * the JDK's to say ({@code CharSequence}, {@code int}) and no declaration of ours settles, so it
 * carries an explicit one.
 *
 * <p>Which kernels are in the last two is written down in
 * {@code TheRuntimeAnswersEveryKernelAtItsDeclaredAbiTest}, which is also what holds every other
 * kernel here to the runtime method its declaration derives.
 */
final class Intrinsics {

    private Intrinsics() {
    }

    /** Emits {@code kernel}, leaving its result on the stack. Throws where this table has no row
     * for it — the language names the kernel and the JVM answers it, so a kernel with no answer here
     * is this backend behind the library. */
    static void emit(BodyGen g, Kernel kernel, Core.Call call) {
        Emit e = TABLE.get(kernel);
        if (e == null) {
            throw new IllegalStateException("the JVM emits nothing for `" + kernel.key() + "`");
        }
        e.emit(g, kernel, call);
    }

    sealed interface Emit permits RuntimeStatic, JdkVirtual, NumericFold, TakesAFunction {
        void emit(BodyGen g, Kernel kernel, Core.Call call);
    }

    /**
     * An {@code invokestatic} to a Souther runtime class, at the descriptor the kernel's declaration
     * gives: each parameter is the boundary form of the declared parameter type, the return the
     * boundary form of the declared result.
     *
     * <p>A descriptor belongs to the callee. Built from the types observed at the call it agrees
     * with the declaration only while no value can arrive narrower than the parameter it goes into,
     * and a sum-typed parameter ends that — the argument's type is the case it happens to be, while
     * the declaration names the sum.
     *
     * <p>Everything a row carries is something the declaration does not settle. Which class and
     * method answer the kernel is one; the order is another — Souther puts the subject last for pipe
     * reading and the runtime method takes it where it takes it, so the row carries the permutation.
     * What a value goes over as is not among them: an argument going into a slot the runtime takes
     * as a reference is boxed, and which slots those are is what the declaration says, so there is
     * nothing to list.
     */
    record RuntimeStatic(ClassDesc owner, String method, int[] argOrder) implements Emit {

        /**
         * @throws IllegalArgumentException where {@code argOrder} is not a permutation of the
         *     arguments. Every argument is emitted exactly once and in some order; one written twice
         *     would evaluate an expression twice and leave the other unevaluated. That is a fact
         *     about this row and is checked where the row is made, not against a declaration this
         *     does not hold.
         */
        RuntimeStatic {
            boolean[] seen = new boolean[argOrder.length];
            for (int src : argOrder) {
                if (src < 0 || src >= seen.length || seen[src]) {
                    throw new IllegalArgumentException(owner.displayName() + "." + method
                            + " takes its arguments in " + Arrays.toString(argOrder)
                            + ", which is no ordering of " + argOrder.length + " of them");
                }
                seen[src] = true;
            }
            argOrder = argOrder.clone();
        }

        /** A copy, because what this answers with is a claim and not a handle on one. Checked once
         *  where the row is written, an array handed back is an array a reader can write into, and
         *  the ordering the check established would hold until somebody did. */
        @Override
        public int[] argOrder() {
            return argOrder.clone();
        }

        public void emit(BodyGen g, Kernel kernel, Core.Call call) {
            KernelSignature declared = g.kernelSignature(kernel);
            pushArguments(g, declared, call, this);
            g.emitInvokeStatic(owner, method, descriptorOf(declared, this));
        }
    }

    /**
     * A kernel taking a function value. The function is not inlined into the call — the kernel is
     * what applies it — so it is materialised as an {@code Fn}, at the parameter types the container
     * it walks supplies.
     *
     * <p>The descriptor is the declaration's, as everywhere else: a declared function parameter is
     * an {@code Fn} at this boundary. What is this row's own is the value, not the shape — a block
     * has to become something the kernel can apply, and at which types is read off the container.
     *
     * <p>{@code container} is which argument that container is; {@code paramTypes} reads the
     * function's parameter types off it. Arguments go on the stack in the order the kernel declares
     * them.
     */
    record TakesAFunction(ClassDesc owner, String method, int container,
                          Function<Type, List<Type>> paramTypes) implements Emit {
        public void emit(BodyGen g, Kernel kernel, Core.Call call) {
            KernelSignature declared = g.kernelSignature(kernel);
            pushArguments(g, declared, call, this);
            g.emitInvokeStatic(owner, method, descriptorOf(declared, this));
        }
    }

    /**
     * An {@code invokevirtual} to a JDK / {@code java.time} class with an explicit descriptor. The
     * first {@code argOrder} entry is the receiver; the rest are stack arguments.
     *
     * <p>The one emitter that reaches a host method without a runtime kernel in between, which is
     * why it is the one that does not derive its descriptor: what a JDK method takes is the JDK's to
     * say ({@code CharSequence}, {@code int}), and no declaration of ours settles it. That is also
     * why it has to be told what it may be used for: a JDK operation named here takes the Souther
     * values at that position without conversion and answers on all of them (ADR-0112). An argument
     * that would have to be changed to fit — an {@code Int} narrowed to an {@code int} — or an
     * operation that refuses some of the values it admits belongs on a kernel, which owns the
     * conversion and the refusal.
     *
     * <p>This carried a {@code l2iArgs} set that narrowed a listed argument with {@code l2i}. It had
     * no entries, and what it offered was the raw narrowing issue #976 is about, in the one place a
     * later kernel taking a host {@code int} would reach for it.
     */
    record JdkVirtual(ClassDesc owner, String method, MethodTypeDesc desc, int[] argOrder)
            implements Emit {
        public void emit(BodyGen g, Kernel kernel, Core.Call call) {
            for (int src : argOrder) {
                g.genExpr(call.args().get(src));
            }
            g.emitInvokeVirtual(owner, method, desc);
        }
    }

    /**
     * {@code List.sum} / {@code List.product}, which the runtime answers with a method per
     * representation.
     *
     * <p>The declaration is polymorphic — a list of a number, answering that number — so its
     * boundary form is a reference, and the runtime holds a specialization for each of the two
     * numbers instead ({@code long}, {@code BigDecimal}). Which one a call takes is read off the
     * type the checker settled for it. That is not the declaration being worked out again: the
     * declaration is known, and what the call adds is which instantiation it is, which is the only
     * thing that can pick between two implementations of one operation.
     *
     * <p>The list argument alone cannot say which: over the empty-list literal its element is the
     * bottom, and the answer came from the position the call was written in.
     */
    record NumericFold(String intMethod, String decimalMethod) implements Emit {
        public void emit(BodyGen g, Kernel kernel, Core.Call call) {
            Type result = call.type();
            if (result != Type.INT && result != Type.DECIMAL) {
                // the checker admits these two and nothing else; anything here is this compiler
                // disagreeing with itself, and emitting the Int kernel for it would answer a wrong
                // number rather than say so
                throw new IllegalStateException("`" + call.fn() + "` reached the backend answering "
                        + Type.show(result) + ", which is neither Int nor Decimal");
            }
            KernelSignature declared = g.kernelSignature(kernel);
            g.genExpr(call.args().get(0));
            String method = result == Type.DECIMAL ? decimalMethod : intMethod;
            g.emitInvokeStatic(CD_Lists, method, MethodTypeDesc.of(boundaryDesc(result),
                    boundaryDesc(declared.parameters().get(0))));
        }
    }

    /**
     * The slots a call to a kernel goes into: the boundary form of each declared parameter, in the
     * order the row puts them on the stack.
     *
     * <p>Pure, and the only statement of what a kernel is called at. What emits the call reads it,
     * and so does what holds this backend to the runtime's own methods — a second derivation
     * written for either would be a second answer for the two to agree on.
     */
    private static ClassDesc[] slotsOf(KernelSignature declared, Emit row) {
        int[] order = row instanceof RuntimeStatic runtime ? runtime.argOrder()
                : identity(declared.parameters().size());
        ClassDesc[] slots = new ClassDesc[order.length];
        for (int j = 0; j < slots.length; j++) {
            slots[j] = boundaryDesc(declared.parameters().get(order[j]));
        }
        return slots;
    }

    /** The descriptor a call to a kernel is emitted at. */
    static MethodTypeDesc descriptorOf(KernelSignature declared, Emit row) {
        return MethodTypeDesc.of(boundaryDesc(declared.result()), slotsOf(declared, row));
    }

    /** And the descriptor the ordered family is emitted at: the same, with the comparator the
     *  runtime method takes ahead of what the declaration names. */
    static MethodTypeDesc descriptorWithComparator(KernelSignature declared, Emit row) {
        ClassDesc[] slots = slotsOf(declared, row);
        ClassDesc[] params = new ClassDesc[slots.length + 1];
        params[0] = CD_Comparator;
        System.arraycopy(slots, 0, params, 1, slots.length);
        return MethodTypeDesc.of(boundaryDesc(declared.result()), params);
    }

    /**
     * Puts {@code call}'s arguments on the stack the way {@code row} takes them, each adapted to the
     * slot its declared parameter fixes.
     *
     * <p>One walk over the same slots the descriptor is built from, so what is emitted and what is
     * described cannot disagree.
     *
     * <p>The adaptation is one step and every argument goes through it. What varies is how the value
     * is produced — a declared function parameter is materialised as an {@code Fn} the kernel can
     * apply, at the parameter types the container it walks supplies, and anything else is the
     * expression — and an arm that produced a value and returned without adapting it would be the
     * declared carrier and the arrived carrier parting company again, in whichever kernels that arm
     * happened to serve.
     */
    private static void pushArguments(BodyGen g, KernelSignature declared, Core.Call call, Emit row) {
        int[] order = row instanceof RuntimeStatic runtime ? runtime.argOrder()
                : identity(declared.parameters().size());
        ClassDesc[] slots = slotsOf(declared, row);
        for (int j = 0; j < order.length; j++) {
            int src = order[j];
            Type arrived = produce(g, call, src, declared.parameters().get(src), row);
            if (slots[j].equals(CD_Object)) {
                // What the runtime takes as a reference, a primitive has to become one for. A no-op
                // for a value that is one already.
                g.emitBox(arrived);
            }
        }
    }

    /** The value the argument at {@code src} leaves on the stack, and what it is. */
    private static Type produce(BodyGen g, Core.Call call, int src, Type parameter, Emit row) {
        Core argument = call.args().get(src);
        if (parameter instanceof Type.FnOf && row instanceof TakesAFunction takes) {
            g.emitFn(argument, takes.paramTypes().apply(call.args().get(takes.container()).type()));
            return argument.type();
        }
        return g.genExpr(argument);
    }

    private static int[] identity(int n) {
        int[] order = new int[n];
        for (int i = 0; i < n; i++) {
            order[i] = i;
        }
        return order;
    }

    /** The JVM type a value takes at a runtime-method boundary: primitives unboxed, containers as
     * their raw interface, a function as an {@code Fn}, everything else (references, type variables,
     * tuples) as {@code Object}.
     *
     * <p>The one reading of a declared type this backend has. What a kernel is called at is built
     * out of it in {@link #slotsOf} and nowhere else, so nothing outside needs it. */
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
        // A declared function parameter is what the runtime applies, which is an `Fn`. Named in
        // this reading rather than in the rows that take one, so that the descriptor of every kernel
        // comes out of one reading of its declaration.
        if (t instanceof Type.FnOf) {
            return CD_Fn;
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

    /** Every kernel this table emits — which is every kernel the language has, less the few
     *  {@code BodyGen} writes out itself. */
    static Set<Kernel> kernels() {
        return TABLE.keySet();
    }

    /**
     * A kernel of the ordered family, over an element whose order lives on its sum: the runtime call
     * this table already holds for it, taking a comparator ahead of what it was already taking.
     *
     * <p>The one place a runtime method takes an argument the declaration does not name. Everything
     * else is the same walk every kernel goes through — the arguments go on the stack where the row
     * puts them and the descriptor says where they went — with the comparator added in front. The
     * caller has put the comparator there and settled nothing else.
     *
     * <p>Both row shapes that can take one. A kernel walking a container takes the container alone;
     * one applying a function takes the function too, as an {@code Fn}.
     */
    static void emitWithComparator(BodyGen g, Kernel kernel, Core.Call call) {
        KernelSignature declared = g.kernelSignature(kernel);
        ClassDesc owner;
        String method;
        Emit row = TABLE.get(kernel);
        switch (row) {
            case RuntimeStatic each -> {
                owner = each.owner();
                method = each.method();
            }
            case TakesAFunction each -> {
                owner = each.owner();
                method = each.method();
            }
            case Emit each -> throw new IllegalStateException("`" + kernel.key() + "` is emitted as "
                    + each + ", which takes no comparator");
            case null -> throw new IllegalStateException(
                    "the JVM emits nothing for `" + kernel.key() + "`");
        }
        pushArguments(g, declared, call, row);
        g.emitInvokeStatic(owner, method, descriptorWithComparator(declared, row));
    }

    /** How each kernel is emitted — read by the test that holds the descriptor invariant. */
    static Map<Kernel, Emit> emitters() {
        return Map.copyOf(TABLE);
    }

    private static int[] order(int... a) {
        return a;
    }

    private static Emit rt(ClassDesc owner, String method, int[] argOrder) {
        return new RuntimeStatic(owner, method, argOrder);
    }

    private static Emit jdk(ClassDesc owner, String method, MethodTypeDesc desc, int[] argOrder) {
        return new JdkVirtual(owner, method, desc, argOrder);
    }

    private static MethodTypeDesc mtd(ClassDesc ret, ClassDesc... params) {
        return MethodTypeDesc.of(ret, params);
    }

    private static Map<Kernel, Emit> buildTable() {
        ClassDesc bool = ConstantDescs.CD_boolean;
        Map<Kernel, Emit> t = new java.util.EnumMap<>(Kernel.class);

        // String — JDK-native instance methods (explicit descriptor); receiver is the last Souther arg.
        t.put(Kernel.STRING_TO_INT, rt(CD_Strings, "toInt", order(0)));
        t.put(Kernel.STRING_TO_DECIMAL, rt(CD_Strings, "toDecimal", order(0)));
        t.put(Kernel.STRING_LENGTH, rt(CD_Strings, "length", order(0)));
        t.put(Kernel.STRING_TRIM, jdk(CD_String, "trim", mtd(CD_String), order(0)));
        t.put(Kernel.STRING_LOWERCASE, jdk(CD_String, "toLowerCase", mtd(CD_String), order(0)));
        t.put(Kernel.STRING_UPPERCASE, jdk(CD_String, "toUpperCase", mtd(CD_String), order(0)));
        t.put(Kernel.STRING_CONTAINS, jdk(CD_String, "contains", mtd(bool, CD_CharSequence), order(1, 0)));
        t.put(Kernel.STRING_STARTS_WITH, jdk(CD_String, "startsWith", mtd(bool, CD_String), order(1, 0)));
        t.put(Kernel.STRING_ENDS_WITH, jdk(CD_String, "endsWith", mtd(bool, CD_String), order(1, 0)));
        t.put(Kernel.STRING_APPEND, jdk(CD_String, "concat", mtd(CD_String, CD_String), order(0, 1)));
        // String — Strings runtime statics.
        // `slice` left the JDK's `substring` when the language settled on code points: the JDK method
        // indexes UTF-16 units, so the conversion — and the abort for an index the string has not
        // got — lives in the runtime rather than in a descriptor here.
        t.put(Kernel.STRING_SLICE, rt(CD_Strings, "slice", order(2, 0, 1)));
        t.put(Kernel.STRING_SPLIT, rt(CD_Strings, "split", order(1, 0)));
        t.put(Kernel.STRING_JOIN, rt(CD_Strings, "join", order(1, 0)));
        t.put(Kernel.STRING_REPLACE, rt(CD_Strings, "replace", order(2, 0, 1)));
        t.put(Kernel.STRING_WORDS, rt(CD_Strings, "words", order(0)));
        t.put(Kernel.STRING_MATCHES, rt(CD_Strings, "matches", order(1, 0)));
        t.put(Kernel.STRING_CHARACTERS, rt(CD_Strings, "characters", order(0)));
        t.put(Kernel.STRING_CODE_POINTS, rt(CD_Strings, "codePoints", order(0)));
        t.put(Kernel.STRING_FROM_INT, rt(CD_Strings, "fromInt", order(0)));
        t.put(Kernel.STRING_CONCAT, rt(CD_Strings, "concat", order(0)));
        t.put(Kernel.STRING_REVERSE, rt(CD_Strings, "reverse", order(0)));
        t.put(Kernel.STRING_REPEAT, rt(CD_Strings, "repeat", order(1, 0)));
        t.put(Kernel.STRING_LINES, rt(CD_Strings, "lines", order(0)));
        t.put(Kernel.STRING_PAD_LEFT, rt(CD_Strings, "padLeft", order(2, 0, 1)));
        t.put(Kernel.STRING_PAD_RIGHT, rt(CD_Strings, "padRight", order(2, 0, 1)));
        t.put(Kernel.STRING_FROM_DECIMAL, rt(CD_Strings, "fromDecimal", order(0)));

        t.put(Kernel.DECIMAL_TO_INT, rt(CD_DecimalMath, "toInt", order(0, 1)));
        t.put(Kernel.DECIMAL_ROUND, rt(CD_DecimalMath, "round", order(0, 1, 2)));

        // List
        t.put(Kernel.LIST_SORT_BY, new TakesAFunction(CD_Lists, "sortBy", 1,
                held -> List.of(((Type.ListOf) held).element())));
        t.put(Kernel.LIST_FIND, new TakesAFunction(CD_Lists, "find", 1,
                held -> List.of(((Type.ListOf) held).element())));
        t.put(Kernel.OPTION_MAP, new TakesAFunction(CD_Options, "map", 1,
                held -> List.of(((Type.OptionOf) held).element())));
        t.put(Kernel.LIST_MAX, rt(CD_Lists, "max", order(0)));
        t.put(Kernel.LIST_MIN, rt(CD_Lists, "min", order(0)));
        t.put(Kernel.LIST_LENGTH, rt(CD_Lists, "length", order(0)));
        t.put(Kernel.LIST_GET, rt(CD_Lists, "get", order(1, 0)));
        t.put(Kernel.LIST_SORT, rt(CD_Lists, "sort", order(0)));
        t.put(Kernel.LIST_REVERSE, rt(CD_Lists, "reverse", order(0)));
        t.put(Kernel.LIST_RANGE_INCLUSIVE, rt(CD_Lists, "rangeInclusive", order(0, 1)));
        t.put(Kernel.LIST_SUM, new NumericFold("sumInt", "sumDecimal"));
        t.put(Kernel.LIST_PRODUCT, new NumericFold("productInt", "productDecimal"));

        // Map
        t.put(Kernel.MAP_GET, rt(CD_Maps, "get", order(1, 0)));
        t.put(Kernel.MAP_EMPTY, rt(CD_Maps, "empty", order()));
        t.put(Kernel.MAP_CONTAINS_KEY, rt(CD_Maps, "containsKey", order(1, 0)));
        t.put(Kernel.MAP_KEYS, rt(CD_Maps, "keys", order(0)));
        t.put(Kernel.MAP_VALUES, rt(CD_Maps, "values", order(0)));
        t.put(Kernel.MAP_SINGLETON, rt(CD_Maps, "singleton", order(0, 1)));
        t.put(Kernel.MAP_INSERT, rt(CD_Maps, "insert", order(0, 1, 2)));
        t.put(Kernel.MAP_REMOVE, rt(CD_Maps, "remove", order(0, 1)));
        t.put(Kernel.MAP_IS_EMPTY, rt(CD_Maps, "isEmpty", order(0)));
        t.put(Kernel.MAP_SIZE, rt(CD_Maps, "size", order(0)));
        t.put(Kernel.MAP_TO_LIST, rt(CD_Maps, "toList", order(0)));
        t.put(Kernel.MAP_FROM_LIST, rt(CD_Maps, "fromList", order(0)));

        // Set
        t.put(Kernel.SET_EMPTY, rt(CD_Sets, "empty", order()));
        t.put(Kernel.SET_SINGLETON, rt(CD_Sets, "singleton", order(0)));
        t.put(Kernel.SET_INSERT, rt(CD_Sets, "insert", order(0, 1)));
        t.put(Kernel.SET_REMOVE, rt(CD_Sets, "remove", order(0, 1)));
        t.put(Kernel.SET_CONTAINS, rt(CD_Sets, "contains", order(0, 1)));
        t.put(Kernel.SET_UNION, rt(CD_Sets, "union", order(0, 1)));
        t.put(Kernel.SET_INTERSECTION, rt(CD_Sets, "intersection", order(0, 1)));
        t.put(Kernel.SET_DIFFERENCE, rt(CD_Sets, "difference", order(0, 1)));
        t.put(Kernel.SET_IS_EMPTY, rt(CD_Sets, "isEmpty", order(0)));
        t.put(Kernel.SET_SIZE, rt(CD_Sets, "size", order(0)));
        t.put(Kernel.SET_TO_LIST, rt(CD_Sets, "toList", order(0)));
        t.put(Kernel.SET_FROM_LIST, rt(CD_Sets, "fromList", order(0)));

        // Date / DateTime — the temporal is the receiver (emitted first); the count is a long.
        // Through the runtime rather than straight to `java.time`: a shift off the end of the range
        // aborts saying what it was doing, instead of the JVM's own exception reaching the boundary
        // and naming a class the language has no type for.
        t.put(Kernel.DATE_ADD_DAYS, rt(CD_Temporals, "addDays", order(1, 0)));
        t.put(Kernel.DATE_ADD_MONTHS, rt(CD_Temporals, "addMonths", order(1, 0)));
        t.put(Kernel.DATE_ADD_YEARS, rt(CD_Temporals, "addYears", order(1, 0)));
        t.put(Kernel.DATE_DAYS_BETWEEN, rt(CD_Temporals, "daysBetween", order(0, 1)));
        t.put(Kernel.DATE_YEAR, rt(CD_Temporals, "year", order(0)));
        t.put(Kernel.DATE_MONTH, rt(CD_Temporals, "month", order(0)));
        t.put(Kernel.DATE_DAY, rt(CD_Temporals, "day", order(0)));
        t.put(Kernel.DATE_FROM_PARTS, rt(CD_Temporals, "fromDateParts", order(0, 1, 2)));
        t.put(Kernel.TIME_FROM_PARTS, rt(CD_Temporals, "fromTimeParts", order(0, 1, 2)));
        t.put(Kernel.TIME_HOUR, rt(CD_Temporals, "hour", order(0)));
        t.put(Kernel.TIME_MINUTE, rt(CD_Temporals, "minute", order(0)));
        t.put(Kernel.TIME_SECOND, rt(CD_Temporals, "second", order(0)));
        t.put(Kernel.DATETIME_ADD_MINUTES, rt(CD_Temporals, "addMinutes", order(1, 0)));
        t.put(Kernel.DATETIME_ADD_HOURS, rt(CD_Temporals, "addHours", order(1, 0)));
        // `addDateTimeDays` rather than a second `addDays`: the runtime is Java, which would take the
        // two as overloads and leave the emitter's descriptor deciding which, where the kernel already
        // says which temporal it is for.
        t.put(Kernel.DATETIME_ADD_DAYS, rt(CD_Temporals, "addDateTimeDays", order(1, 0)));
        t.put(Kernel.DATETIME_MINUTES_BETWEEN, rt(CD_Temporals, "minutesBetween", order(0, 1)));
        t.put(Kernel.DATETIME_TO_DATE,
                jdk(CD_LocalDateTime, "toLocalDate", mtd(CD_LocalDate), order(0)));
        t.put(Kernel.DATETIME_TO_TIME,
                jdk(CD_LocalDateTime, "toLocalTime", mtd(CD_LocalTime), order(0)));
        // A date and a time of day are both settled values, so joining them cannot fail: total, with
        // the date as the receiver of `LocalDate.atTime`.
        t.put(Kernel.DATETIME_FROM_DATE_AND_TIME,
                jdk(CD_LocalDate, "atTime", mtd(CD_LocalDateTime, CD_LocalTime), order(0, 1)));

        // Int — IntMath statics. add/subtract/multiply share the overflow-aborting kernel with the
        // `+ - *` operators; modBy aborts on a zero divisor; compare returns -1/0/1.
        t.put(Kernel.INT_ADD, rt(CD_IntMath, "addExact", order(0, 1)));
        t.put(Kernel.INT_SUBTRACT, rt(CD_IntMath, "subtractExact", order(0, 1)));
        t.put(Kernel.INT_MULTIPLY, rt(CD_IntMath, "multiplyExact", order(0, 1)));
        t.put(Kernel.INT_COMPARE, rt(CD_IntMath, "compare", order(0, 1)));
        t.put(Kernel.INT_FLOOR_MOD, rt(CD_IntMath, "floorMod", order(0, 1)));

        // Decimal — every one of them a DecimalMath static. What a BigDecimal method does is not
        // what a Souther operation means: each of these is partial at
        // the ends of the scale range, and the abort that reports it belongs to the operation rather
        // than to whoever emitted the call (ADR-0112). One emitter for the whole module, so a
        // Decimal operation added later has one place to be written and no second shape to pick.
        t.put(Kernel.DECIMAL_ADD, rt(CD_DecimalMath, "add", order(0, 1)));
        t.put(Kernel.DECIMAL_SUBTRACT, rt(CD_DecimalMath, "subtract", order(0, 1)));
        t.put(Kernel.DECIMAL_MULTIPLY, rt(CD_DecimalMath, "multiply", order(0, 1)));
        t.put(Kernel.DECIMAL_DIVIDE, rt(CD_DecimalMath, "divide", order(0, 1, 2, 3)));
        t.put(Kernel.DECIMAL_COMPARE, rt(CD_DecimalMath, "compare", order(0, 1)));
        t.put(Kernel.DECIMAL_FROM_INT, rt(CD_DecimalMath, "fromInt", order(0)));

        // Not a copy: the map is a local nothing else holds, and read back through an EnumMap it
        // answers in the order the kernels are declared in rather than in whatever order a copy
        // happens to hash them into.
        return java.util.Collections.unmodifiableMap(t);
    }
}
