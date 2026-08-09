package souther.compiler.codegen;

import souther.compiler.ast.Ast;
import souther.compiler.ast.WrittenName;
import souther.compiler.check.BehaviorRequirement;
import souther.compiler.check.Requirements;
import souther.compiler.check.Sig;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.msg.DeclarationMessage;
import souther.compiler.diag.DiagnosticCode;
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

    /** What it says when it will not write the pool out at all. The other way it reaches the same
     *  limit: this one is measured after everything is pooled, rather than at a reference into it. */
    private static final Pattern POOL_SIZE =
            Pattern.compile("Constant pool is too large (\\d+)\\s*", Pattern.DOTALL);

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
                    throw tooWide(Wide.DATA, data.written(), slots, INSTANCE_SLOTS,
                            "data `" + data.name() + "` needs " + slots + " JVM parameter slots, but the"
                                    + " constructor generated for it takes at most " + INSTANCE_SLOTS);
                }
            }
        }
        // What a class is written for, which is both components: the limit is the JVM's and does not
        // ask who declared the fn.
        Set<String> implemented = new HashSet<>();
        for (Ast.FnDef fn : module.fns()) {
            implemented.add(fn.name());
        }
        for (Ast.FnDef fn : module.takenOn()) {
            implemented.add(fn.name());
        }
        for (Ast.BehaviorDef bd : module.behaviors()) {
            Sig sig = sigs.get(bd.name());
            // a composition whose stage names nothing has no signature, and nothing is emitted for it
            if (sig != null && sig.inputTypes().size() > INSTANCE_SLOTS) {
                throw tooWide(Wide.BEHAVIOR_PARAMETERS, bd.written(), sig.inputTypes().size(),
                        INSTANCE_SLOTS, "behavior `" + bd.name() + "` takes " + sig.inputTypes().size()
                                + " parameters, but the `apply` generated for it takes at most "
                                + INSTANCE_SLOTS);
            }
            int dependencies = dependencyCount(bd, implemented, requirements);
            // the $Impl constructor holds one field per dependency, and it is an instance method
            if (dependencies > INSTANCE_SLOTS) {
                throw tooWide(Wide.BEHAVIOR_DEPENDENCIES, bd.written(), dependencies,
                        INSTANCE_SLOTS, "behavior `" + bd.name() + "` is built with " + dependencies
                                + " dependencies, but the constructor generated for it takes at most "
                                + INSTANCE_SLOTS);
            }
        }
        for (Ast.FnDef helper : recursiveHelpers.values()) {
            // a recursive helper is a static method on $Fns, so nothing is spent on `this`
            if (helper.params().size() > SLOTS) {
                throw tooWide(Wide.HELPER, helper.written(), helper.params().size(),
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

    /**
     * A structural limit of the class file format, as the writer refused to go past it.
     *
     * <p>The pool is two of them because the writer reaches it two ways, and the number it hands back
     * is not the same number: refusing to refer to an entry it cannot address says which entry was
     * wanted, and refusing to write the pool out says how many entries there are.
     */
    enum Limit {
        CODE_SIZE(DiagnosticCode.E2102),
        CONSTANT_POOL_INDEX(DiagnosticCode.E2103),
        CONSTANT_POOL_SIZE(DiagnosticCode.E2103);

        private final DiagnosticCode code;

        Limit(DiagnosticCode code) {
            this.code = code;
        }
    }

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
        Matcher index = POOL_INDEX.matcher(said);
        if (index.matches()) {
            long wanted = Long.parseLong(index.group(1));
            return wanted > POOL_ENTRIES ? new Exceeded(Limit.CONSTANT_POOL_INDEX, wanted, null) : null;
        }
        Matcher size = POOL_SIZE.matcher(said);
        if (size.matches()) {
            long entries = Long.parseLong(size.group(1));
            return entries > POOL_ENTRIES ? new Exceeded(Limit.CONSTANT_POOL_SIZE, entries, null) : null;
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
    static CompileException tooLarge(Exceeded exceeded, WrittenName written) {
        Limit limit = exceeded.limit();
        String name = written.canonical();
        String measured = String.valueOf(exceeded.measured());
        Diagnostic.Builder said = Diagnostic.at(written.region());
        return switch (limit) {
            case CODE_SIZE -> CompileException.of(said
                    .say(new DeclarationMessage.AMethodIsLargerThanTheJvmHolds(name,
                            exceeded.method(), measured, String.valueOf(CODE_BYTES)))
                    .hint(new DeclarationMessage.SplitTheWorkOrMoveTheTable()).build());
            case CONSTANT_POOL_INDEX -> CompileException.of(said
                    .say(new DeclarationMessage.AClassRefersPastTheConstantPool(name, measured,
                            String.valueOf(POOL_ENTRIES)))
                    .hint(new DeclarationMessage.MoveTheTableOutOfTheSource()).build());
            case CONSTANT_POOL_SIZE -> CompileException.of(said
                    .say(new DeclarationMessage.AClassNeedsMoreConstantsThanItHolds(name, measured,
                            String.valueOf(POOL_ENTRIES)))
                    .hint(new DeclarationMessage.MoveTheTableOutOfTheSource()).build());
        };
    }

    /** Which definition ran out of parameter slots. */
    private enum Wide { DATA, BEHAVIOR_PARAMETERS, BEHAVIOR_DEPENDENCIES, HELPER }

    private static CompileException tooWide(Wide what, WrittenName written, int needed,
                                            int limit, String message) {
        String name = written.canonical();
        String has = String.valueOf(needed);
        String holds = String.valueOf(limit);
        return CompileException.of(Diagnostic.at(written.region())
                .say(switch (what) {
                    case DATA -> new DeclarationMessage.ADataNeedsMoreSlotsThanAConstructorHolds(
                            name, has, holds);
                    case HELPER ->
                            new DeclarationMessage.AHelperTakesMoreParametersThanAMethodHolds(name,
                                    has, holds);
                    case BEHAVIOR_PARAMETERS ->
                            new DeclarationMessage.ABehaviorTakesMoreParametersThanApplyHolds(name,
                                    has, holds);
                    case BEHAVIOR_DEPENDENCIES ->
                            new DeclarationMessage
                                    .ABehaviorHasMoreDependenciesThanAConstructorHolds(name, has,
                                            holds);
                })
                .hint(switch (what) {
                    case DATA -> new DeclarationMessage.SplitTheDataAndHoldThemAsFields(name);
                    case BEHAVIOR_DEPENDENCIES ->
                            new DeclarationMessage.GroupTheDependenciesBehindABehavior();
                    default -> new DeclarationMessage.GroupTheParametersIntoAData();
                })
                .build());
    }
}
