package souther.compiler.codegen;

import souther.compiler.DefaultStdlib;
import souther.compiler.core.Kernel;
import souther.compiler.core.KernelSignature;

import org.junit.jupiter.api.Test;

import java.lang.constant.ClassDesc;
import java.lang.constant.MethodTypeDesc;
import java.lang.invoke.MethodType;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.EnumSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What a kernel's declaration says it takes, the runtime has a method for.
 *
 * <p>The descriptor of a runtime kernel is derived: parameters and return are the boundary forms of
 * the declared ones, and nothing about the call goes into it. That makes it a claim about two
 * artifacts that are built apart — the {@code .sou} declarations this compiler ships, and the
 * methods {@code souther-runtime} declares — and no construction can hold it, because neither side
 * knows the other. Held here, by asking for the descriptor a call is emitted at and asking the
 * runtime class whether it has that method.
 *
 * <p>This replaces the invariant that used to say a descriptor built from the call agreed with the
 * declaration where nothing could arrive narrower. There is no descriptor built from a call left to
 * say it of; what is worth saying now is that the one rule reaches something real.
 *
 * <p>Asked with {@link Intrinsics#descriptorOf}, which is what the emitter calls the method at. A
 * derivation written here instead would be a second answer for the two to agree on, and the day
 * they differed this would be holding the runtime to a rule nothing emits.
 *
 * <p>Both forms a kernel can be called at. The ordered family reaches its runtime method with a
 * comparator ahead of what the declaration names, and that is a second method — held here too, off
 * the kernels {@code BodyGen}'s arm is driven by.
 */
class TheRuntimeAnswersEveryKernelAtItsDeclaredAbiTest {

    /**
     * The kernels the runtime answers with a method per representation rather than at the
     * declaration's own boundary form.
     *
     * <p>{@code List.sum} is declared over any number and answered by a {@code long} or a
     * {@code BigDecimal}; the declared result is the type variable, whose boundary form is a
     * reference. Which method a call takes is the type the checker settled for it — an instantiation
     * choosing between two implementations of one operation, and the only thing left that a
     * call-site type decides.
     */
    private static final Set<Kernel> ANSWERED_PER_REPRESENTATION =
            EnumSet.of(Kernel.LIST_SUM, Kernel.LIST_PRODUCT);

    /**
     * The kernels emitted as a call to a JDK method, whose descriptor is the JDK's to say
     * ({@code CharSequence}, {@code int}) and no declaration of ours settles.
     */
    private static final Set<Kernel> ANSWERED_BY_THE_HOST = EnumSet.of(
            Kernel.STRING_TRIM, Kernel.STRING_LOWERCASE, Kernel.STRING_UPPERCASE,
            Kernel.STRING_CONTAINS, Kernel.STRING_STARTS_WITH, Kernel.STRING_ENDS_WITH,
            Kernel.STRING_APPEND, Kernel.DATETIME_TO_DATE, Kernel.DATETIME_TO_TIME,
            Kernel.DATETIME_FROM_DATE_AND_TIME);

    @Test
    void everyRuntimeKernelIsAnsweredAtTheDescriptorItsDeclarationGives() {
        List<String> unanswered = new ArrayList<>();
        for (Map.Entry<Kernel, Intrinsics.Emit> row : Intrinsics.emitters().entrySet()) {
            Kernel kernel = row.getKey();
            if (ANSWERED_PER_REPRESENTATION.contains(kernel)
                    || ANSWERED_BY_THE_HOST.contains(kernel)) {
                continue;
            }
            KernelSignature declared = declared(kernel);
            String missing = whatTheRuntimeHasInstead(row.getValue(),
                    Intrinsics.descriptorOf(declared, row.getValue()));
            if (missing != null) {
                unanswered.add(kernel.key() + ": " + missing);
            }
            // And the ordered family's other method, which takes a comparator the declaration does
            // not name ahead of the arguments it does.
            if (BodyGen.ORDERED_BY_COMPARATOR.contains(kernel)) {
                String ordered = whatTheRuntimeHasInstead(row.getValue(),
                        Intrinsics.descriptorWithComparator(declared, row.getValue()));
                if (ordered != null) {
                    unanswered.add(kernel.key() + " with a comparator: " + ordered);
                }
            }
        }

        assertEquals(List.of(), unanswered,
                "the descriptor a kernel's declaration gives names no method the runtime has —"
                        + " either the declaration moved and the runtime did not, or the other way");
    }

    /**
     * And these are the only kernels outside that rule.
     *
     * <p>The sets and not their sizes. Counted, a kernel moving into the host family and another
     * moving out of it is two changes that cancel, and a kernel stops being held to its declaration
     * with nothing said. Written out, a new exception is a deliberate edit here as well as there.
     */
    @Test
    void andTheseAreTheOnlyKernelsThatAreNot() {
        Set<Kernel> perRepresentation = EnumSet.noneOf(Kernel.class);
        Set<Kernel> byTheHost = EnumSet.noneOf(Kernel.class);
        for (Map.Entry<Kernel, Intrinsics.Emit> row : Intrinsics.emitters().entrySet()) {
            switch (row.getValue()) {
                case Intrinsics.NumericFold _ -> perRepresentation.add(row.getKey());
                case Intrinsics.JdkVirtual _ -> byTheHost.add(row.getKey());
                case Intrinsics.RuntimeStatic _, Intrinsics.TakesAFunction _ -> { }
            }
        }

        assertEquals(ANSWERED_PER_REPRESENTATION, perRepresentation,
                "which kernels the runtime answers with a method per representation");
        assertEquals(ANSWERED_BY_THE_HOST, byTheHost,
                "which kernels are answered by a JDK method");
    }

    /**
     * And these are the kernels reached through the comparator method.
     *
     * <p>The set the arm in {@code BodyGen} is driven by, so a kernel routed there is a kernel this
     * asks the comparator descriptor of. Held here as well because membership is not decided by any
     * of that: whether a kernel takes the enumeration's order is what a program answers, and the
     * witness for each of these is a case in {@code CompileEnumerationOrderTest} that sorts, takes
     * the extremes of, or keys a list of cases and reads the result. A kernel added to the set and
     * to nothing else is emitted differently with nothing running it that way.
     */
    @Test
    void andTheseAreTheKernelsReachedThroughTheComparator() {
        assertEquals(
                EnumSet.of(Kernel.LIST_SORT, Kernel.LIST_SORT_BY, Kernel.LIST_MAX, Kernel.LIST_MIN),
                EnumSet.copyOf(BodyGen.ORDERED_BY_COMPARATOR),
                "which kernels reach a runtime method taking a comparator — each wants a case in"
                        + " CompileEnumerationOrderTest that runs it over an enumeration");
    }

    /**
     * And a row does not hand out the ordering it was checked for.
     *
     * <p>{@code RuntimeStatic} refuses an {@code argOrder} that is no ordering of its arguments, and
     * a check made once on a value a reader can write into holds until a reader writes into it. The
     * descriptor and the arguments are both derived from this, so an ordering edited afterwards
     * would emit a call at a shape nothing refused.
     */
    @Test
    void andARowDoesNotHandOutTheOrderingItWasCheckedFor() {
        Intrinsics.RuntimeStatic row = (Intrinsics.RuntimeStatic)
                Intrinsics.emitters().get(Kernel.STRING_SLICE);
        int[] taken = row.argOrder();

        taken[0] = taken[0] + 1;

        assertEquals(2, row.argOrder()[0], "the row still takes its arguments in the order it was"
                + " written with");
    }

    /**
     * And a row takes as many arguments as its kernel declares.
     *
     * <p>The half {@code RuntimeStatic} cannot check for itself. It refuses an {@code argOrder} that
     * is no ordering of its own length, which is a fact about the row; that the length is the
     * kernel's arity is a fact about the two together, and a row one short would derive a descriptor
     * for a call it emitted the wrong number of arguments for.
     *
     * <p>Of the rows that carry a count. A kernel applying a function walks the declaration's own
     * parameters and a numeric fold takes the one it is declared with, so for those two there is no
     * second number to disagree with the first.
     */
    @Test
    void andEachRowTakesAsManyArgumentsAsItsKernelDeclares() {
        List<String> disagreeing = new ArrayList<>();
        for (Map.Entry<Kernel, Intrinsics.Emit> row : Intrinsics.emitters().entrySet()) {
            int declared = declared(row.getKey()).parameters().size();
            int taken = switch (row.getValue()) {
                case Intrinsics.RuntimeStatic r -> r.argOrder().length;
                case Intrinsics.JdkVirtual r -> r.argOrder().length;
                case Intrinsics.TakesAFunction _, Intrinsics.NumericFold _ -> declared;
            };
            if (taken != declared) {
                disagreeing.add(row.getKey().key() + " is emitted with " + taken
                        + " argument(s) and declares " + declared);
            }
        }

        assertEquals(List.of(), disagreeing, "a row emits a different number of arguments than the"
                + " kernel it answers declares");
    }

    /** What the language declares {@code kernel} to take and answer. */
    private static KernelSignature declared(Kernel kernel) {
        return DefaultStdlib.get().kernelSignatures().signatureOf(kernel);
    }

    /**
     * Null where the runtime has a static {@code method} of exactly {@code want}, and otherwise what
     * it has under that name — so a failure says what to change rather than that something differs.
     */
    private static String whatTheRuntimeHasInstead(Intrinsics.Emit row, MethodTypeDesc want) {
        ClassDesc owner;
        String name;
        switch (row) {
            case Intrinsics.RuntimeStatic each -> {
                owner = each.owner();
                name = each.method();
            }
            case Intrinsics.TakesAFunction each -> {
                owner = each.owner();
                name = each.method();
            }
            default -> throw new IllegalStateException(row + " reaches no runtime static");
        }
        String owning = owner.packageName().isEmpty() ? owner.displayName()
                : owner.packageName() + "." + owner.displayName();
        List<String> under = new ArrayList<>();
        Class<?> runtime;
        try {
            runtime = Class.forName(owning);
        } catch (ClassNotFoundException absent) {
            return "the runtime has no class " + owning;
        }
        for (Method candidate : runtime.getDeclaredMethods()) {
            if (!candidate.getName().equals(name) || !Modifier.isStatic(candidate.getModifiers())) {
                continue;
            }
            String has = MethodType.methodType(candidate.getReturnType(),
                    candidate.getParameterTypes()).descriptorString();
            if (has.equals(want.descriptorString())) {
                return null;
            }
            under.add(has);
        }
        return owning + "." + name + " is derived as " + want.descriptorString()
                + " and the runtime declares " + under;
    }
}
