package souther.compiler.codegen;

import souther.compiler.ast.Ast;
import souther.compiler.check.BehaviorRequirement;
import souther.compiler.check.Requirements;
import souther.compiler.check.Sig;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.Type;

import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * What the JVM will hold, asked of a declaration before anything is emitted for it.
 *
 * <p>A method signature takes at most 255 argument slots, and an instance method spends one of them
 * on {@code this}. Nothing in the emitter notices when a declaration needs more: the class is
 * written, and the JVM refuses it at load time with a {@code ClassFormatError} naming its own rule
 * rather than the declaration that broke it. So the count is taken here, where the declaration and
 * its position are both in hand.
 *
 * <p>The count is of slots, not of fields: an {@code Int} is carried as a {@code long} and takes
 * two. A behavior's parameter is not — an {@code apply} takes every parameter as a reference — so
 * the two are counted by different rules, which is why the limit falls at a different width for
 * each.
 */
final class JvmLimits {

    /** The argument slots one JVM method signature holds (JVMS 4.3.3). */
    private static final int SLOTS = 255;

    /** The same, for an instance method, whose {@code this} takes the first of them. */
    private static final int INSTANCE_SLOTS = SLOTS - 1;

    /** The bytes of code one method's {@code Code} attribute holds (JVMS 4.7.3). */
    private static final int CODE_BYTES = 65535;

    /** The entries one class file's constant pool holds (JVMS 4.4). */
    private static final int POOL_ENTRIES = 65535;

    /** What the class file writer says when it will not write a method's code. Matches the empty
     *  body too, which is the same sentence and not this limit. */
    private static final Pattern CODE_LENGTH =
            Pattern.compile("Code length (\\d+) is outside the allowed range in ([^(]*)\\(.*",
                    Pattern.DOTALL);

    /** What it says when a constant it is referring to is not in the pool — because the pool
     *  overflowed, or because the entry was never pooled, which is not this limit. */
    private static final Pattern POOL_INDEX =
            Pattern.compile("(-?\\d+) is not a valid index\\..*", Pattern.DOTALL);

    private JvmLimits() {}

    /**
     * Reports the first declaration whose generated method would take more argument slots than a JVM
     * method signature holds.
     *
     * <p>{@code sigs} is what each behavior's {@code apply} is generated from, so a composition —
     * which declares no parameters of its own and takes the first stage's — is counted by what will
     * be emitted rather than by what it wrote. {@code requirements} likewise carries the dependencies
     * a composition is built with, which are the stages' and not its own.
     */
    static void checkParameterSlots(Ast.Module module, CodegenContext ctx,
                                    Map<String, Ast.FnDef> recursiveHelpers,
                                    Map<String, Sig> sigs,
                                    Map<String, List<BehaviorRequirement>> requirements) {
        for (Ast.Def def : module.defs()) {
            if (def instanceof Ast.Data data) {
                int slots = 0;
                for (Type field : ctx.fieldTypes(data).values()) {
                    slots += JvmTypes.width(field);
                }
                // the record constructor takes them all, and it is an instance method
                if (slots > INSTANCE_SLOTS) {
                    throw tooWide("e2101.data", data.pos(), data.name(), slots, INSTANCE_SLOTS,
                            "data `" + data.name() + "` needs " + slots + " JVM parameter slots, but the"
                                    + " constructor generated for it takes at most " + INSTANCE_SLOTS);
                }
            }
        }
        Set<String> implemented = new HashSet<>();
        for (Ast.FnDef fn : module.fns()) {
            implemented.add(fn.name());
        }
        for (Ast.BehaviorDef bd : module.behaviors()) {
            Sig sig = sigs.get(bd.name());
            // a composition whose stage names nothing has no signature, and nothing is emitted for it
            if (sig != null && sig.ins().size() > INSTANCE_SLOTS) {
                throw tooWide("e2101.behavior.parameters", bd.pos(), bd.name(), sig.ins().size(),
                        INSTANCE_SLOTS, "behavior `" + bd.name() + "` takes " + sig.ins().size()
                                + " parameters, but the `apply` generated for it takes at most "
                                + INSTANCE_SLOTS);
            }
            int dependencies = dependencyCount(bd, implemented, requirements);
            // the $Impl constructor holds one field per dependency, and it is an instance method
            if (dependencies > INSTANCE_SLOTS) {
                throw tooWide("e2101.behavior.dependencies", bd.pos(), bd.name(), dependencies,
                        INSTANCE_SLOTS, "behavior `" + bd.name() + "` is built with " + dependencies
                                + " dependencies, but the constructor generated for it takes at most "
                                + INSTANCE_SLOTS);
            }
        }
        for (Ast.FnDef helper : recursiveHelpers.values()) {
            // a recursive helper is a static method on $Fns, so nothing is spent on `this`
            if (helper.params().size() > SLOTS) {
                throw tooWide("e2101.helper", helper.pos(), helper.name(), helper.params().size(),
                        SLOTS, "let `" + helper.name() + "` takes " + helper.params().size()
                                + " parameters, but the method generated for it takes at most " + SLOTS);
            }
        }
    }

    /**
     * How many dependencies the behavior's generated constructor holds.
     *
     * <p>An injection target has none — Java implements it, and its generated base has a constructor
     * of its own. A behavior a {@code let} implements holds what it declared. A composition holds what
     * its stages need, worked out for it, so what it wrote is not the count.
     */
    private static int dependencyCount(Ast.BehaviorDef bd, Set<String> implemented,
                                       Map<String, List<BehaviorRequirement>> requirements) {
        if (bd instanceof Ast.SpecBehavior spec) {
            return implemented.contains(spec.name()) ? spec.dependsOn().size() : 0;
        }
        return Requirements.names(requirements.getOrDefault(bd.name(), List.of())).size();
    }

    /** A structural limit of the class file format, as the writer refused to go past it. */
    enum Limit { CODE_SIZE, CONSTANT_POOL }

    /**
     * A refusal read as the limit it was: which one, the number that went past it, and the method
     * being written when it did — {@code null} for a limit the writer does not attribute to one.
     */
    record Exceeded(Limit limit, long measured, String method) {}

    /**
     * The limit {@code e} says was exceeded, or {@code null} if it says something else.
     *
     * <p>The writer refuses an empty method body and an oversized one with the same sentence, and an
     * index of zero with the same sentence as an index past the pool's last entry. Only the number
     * separates a declaration that is too large from this compiler emitting something it should not
     * have, so a refusal is a diagnostic only where the number puts it past the limit.
     */
    static Exceeded exceeded(IllegalArgumentException e) {
        String said = e.getMessage();
        if (said == null) {
            return null;
        }
        Matcher code = CODE_LENGTH.matcher(said);
        if (code.matches()) {
            long length = Long.parseLong(code.group(1));
            return length > CODE_BYTES ? new Exceeded(Limit.CODE_SIZE, length, code.group(2)) : null;
        }
        Matcher pool = POOL_INDEX.matcher(said);
        if (pool.matches()) {
            long index = Long.parseLong(pool.group(1));
            return index > POOL_ENTRIES ? new Exceeded(Limit.CONSTANT_POOL, index, null) : null;
        }
        return null;
    }

    /**
     * The refusal, said as the definition that was being emitted when it came.
     *
     * <p>Which method of it the writer named is carried into the message: a data is emitted as a
     * value class, a decoder and an encoder, and a behavior as an implementation and an interface, so
     * naming the definition alone would leave the author looking for which part of it grew.
     */
    static CompileException tooLarge(Exceeded exceeded, SourcePos pos, String name) {
        if (exceeded.limit() == Limit.CODE_SIZE) {
            return CompileException.of(
                    Diagnostic.of("E2102", "e2102.msg").at(pos, name.length())
                            .args(name, exceeded.method(), String.valueOf(exceeded.measured()),
                                    String.valueOf(CODE_BYTES))
                            .hint("e2102.hint").build(),
                    "the `" + exceeded.method() + "` method generated for `" + name + "` is "
                            + exceeded.measured() + " bytes of code, but a JVM method holds at most "
                            + CODE_BYTES);
        }
        return CompileException.of(
                Diagnostic.of("E2103", "e2103.msg").at(pos, name.length())
                        .args(name, String.valueOf(exceeded.measured()), String.valueOf(POOL_ENTRIES))
                        .hint("e2103.hint").build(),
                "the class generated for `" + name + "` needs constant-pool entry "
                        + exceeded.measured() + ", and a class file holds at most " + POOL_ENTRIES);
    }

    private static CompileException tooWide(String key, SourcePos pos, String name, int needed,
                                            int limit, String message) {
        return CompileException.of(
                Diagnostic.of("E2101", key).at(pos, name.length())
                        .args(name, String.valueOf(needed), String.valueOf(limit))
                        .hint(key + ".hint").build(),
                message);
    }
}
