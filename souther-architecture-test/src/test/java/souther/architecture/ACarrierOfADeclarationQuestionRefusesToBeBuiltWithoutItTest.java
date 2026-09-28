package souther.architecture;

import souther.compiler.check.DeclarationKinds;

import org.junit.jupiter.api.Test;

import java.lang.classfile.Attributes;
import java.lang.classfile.ClassModel;
import java.lang.classfile.CodeElement;
import java.lang.classfile.Instruction;
import java.lang.classfile.Label;
import java.lang.classfile.MethodModel;
import java.lang.classfile.Opcode;
import java.lang.classfile.attribute.RecordAttribute;
import java.lang.classfile.attribute.RecordComponentInfo;
import java.lang.classfile.instruction.BranchInstruction;
import java.lang.classfile.instruction.InvokeInstruction;
import java.lang.classfile.instruction.LabelTarget;
import java.lang.classfile.instruction.LoadInstruction;
import java.lang.classfile.instruction.LookupSwitchInstruction;
import java.lang.classfile.instruction.ReturnInstruction;
import java.lang.classfile.instruction.TableSwitchInstruction;
import java.lang.classfile.instruction.ThrowInstruction;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A value that holds a question about the declarations refuses to be built without it.
 *
 * <p>The questions a reader asks of a declaration it did not write are separate on purpose: which
 * form it is, what it wraps, what its fields hold, what it says. A reader asks the ones it uses, so
 * which of them a value holds differs from value to value and there is no one carrier to put them
 * in — and a value that holds one has been handed it by whoever built it, which is where handing it
 * nothing goes wrong.
 *
 * <p><b>Why this is a rule.</b> A carrier says which questions it holds in its component list and
 * refuses the ones it holds where it is built. The two say the same thing until a question is added
 * to one of them: {@code CheckContext} took what each field holds as a peer of what a name wraps,
 * said so where it is declared, and went on accepting nothing for it. Every production caller
 * filled it in, so nothing failed.
 *
 * <p><b>Why it reads the classes and not the source.</b> A rule over the text is a rule about a
 * spelling, and the language admits more spellings than one can be written against: a component
 * whose type is written out with its package, a record that takes a type parameter, a refusal
 * spelled {@code requireNonNull}, a condition written after a block. A record's components and what
 * its constructor does with them are the language's own answers, so this asks for those instead.
 *
 * <p><b>What a refusal is.</b> Reading the value and deciding something about it is not refusing
 * it: a carrier that puts a default in its place, or says so and carries on, has looked and been
 * built anyway. So what is established is the construction, and not the look — where the value is
 * nothing, the constructor does not return.
 */
class ACarrierOfADeclarationQuestionRefusesToBeBuiltWithoutItTest {

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    /** That and this test's own subjects, which are compiled beside it. */
    private static final CompiledOutputs INCLUDING_THESE =
            CompiledOutputs.ofEverythingCompiledHere();

    /**
     * The questions, by the type a component of one holds.
     *
     * <p>Named here rather than found by what implements something. They are separate interfaces
     * because they are separate questions, so there is nothing they share for this to look for —
     * and a marker they all carried would be a category invented to let this be written.
     *
     * <p>{@code DeclarationAccess} is among them though it is no question of its own: it holds
     * several of them together, and a carrier handed nothing for it has been handed nothing for
     * every one of those.
     */
    private static final Set<String> QUESTIONS = Set.of(
            "Lsouther/compiler/check/PublishedDeclarations;",
            "Lsouther/compiler/check/DeclarationKinds;",
            "Lsouther/compiler/check/NewtypeInners;",
            "Lsouther/compiler/check/EffectiveFieldTypes;",
            "Lsouther/compiler/check/FieldLayout;",
            "Lsouther/compiler/check/DeclarationAccess;",
            "Lsouther/compiler/check/DeclarationNewtypes;",
            "Lsouther/compiler/check/FieldBindings;",
            "Lsouther/compiler/check/ClauseLocations;",
            "Lsouther/compiler/check/ExpandedClauseLookup;",
            "Lsouther/compiler/check/DeclarationLocations;");

    /**
     * The one carrier this does not ask it of, by the whole of what it is.
     *
     * <p>{@code CheckContext.Same} is a context being written out of another one: it is built from
     * the components of a {@code CheckContext} that has already refused them, and there is no path
     * that hands it anything else. A condition of its own would never be reached, and a law about
     * an unreachable state reads as a case somebody had thought about.
     *
     * <p>Said by its owner and not by its name. There is a second {@code Same} in this repository
     * and there will be others; an exception written as a name is an exception to whichever of them
     * comes to hold one of these questions.
     */
    private static final String BUILT_FROM_A_CARRIER_THAT_REFUSED_THEM =
            "souther/compiler/check/CheckContext$Same";

    @Test
    void everyCarrierThatHoldsOneRefusesToBeBuiltWithoutIt() {
        List<String> accepted = new ArrayList<>();
        List<String> carriers = new ArrayList<>();
        for (ClassModel model : COMPILED.all()) {
            String carrier = model.thisClass().asInternalName();
            if (questionsHeldBy(model).isEmpty()
                    || carrier.equals(BUILT_FROM_A_CARRIER_THAT_REFUSED_THEM)) {
                continue;
            }
            carriers.add(carrier);
            accepted.addAll(builtWithoutAQuestionIt(model));
        }

        assertTrue(carriers.size() > 5,
                () -> "only these carriers were found, so this scanned nothing: " + carriers);
        assertEquals(List.of(), accepted,
                "a carrier that holds a question about the declarations and is built without it"
                        + " — the component was added to what it holds and not to what refuses it");
    }

    /**
     * A carrier that looks and is built anyway is built without it, and one over a type parameter
     * is read like any other.
     *
     * <p>Both of the subjects below, because both are what the rule above would otherwise be said
     * to hold without anything establishing it. A rule that took a look for a refusal would pass
     * {@link LooksAndCarriesOn}; one whose population came from a shape narrower than the language's
     * would not see either of them at all.
     *
     * <p>And the one that does refuse, beside them. Without it this is met by a rule that reports
     * every carrier, which reports the right ones for the wrong reason.
     */
    @Test
    void aCarrierThatLooksWithoutRefusingIsBuiltWithoutItAndATypeParameterIsNoEscape() {
        assertEquals(List.of("kinds"), questionsHeldBy(compiled(LooksAndCarriesOn.class)),
                "the subject is supposed to hold one of the questions");
        assertEquals(List.of(subjectName(LooksAndCarriesOn.class) + " holds kinds and is built"
                        + " without it"),
                builtWithoutAQuestionIt(compiled(LooksAndCarriesOn.class)),
                "it reads whether it was handed one and is built either way, and this called that"
                        + " a refusal");
        assertEquals(List.of(), builtWithoutAQuestionIt(compiled(Refuses.class)),
                "and the one that does not return without it is not reported");
    }

    /**
     * A carrier over a type parameter that looks at the question and is built anyway.
     *
     * <p>A default in the place of the answer, which is the shape a refusal is easiest to be
     * mistaken for: the value is loaded, something is decided about it, and the construction
     * happens.
     */
    record LooksAndCarriesOn<A>(A value, DeclarationKinds kinds) {

        LooksAndCarriesOn {
            if (kinds == null) {
                kinds = DeclarationKinds.NONE;
            }
        }
    }

    /** The same, refusing. Beside the one above so that reporting both is not how this passes. */
    record Refuses<A>(A value, DeclarationKinds kinds) {

        Refuses {
            if (kinds == null) {
                throw new IllegalArgumentException("a reading asks which form a declaration is");
            }
        }
    }

    private static String subjectName(Class<?> subject) {
        return subject.getName().replace('.', '/');
    }

    private static ClassModel compiled(Class<?> subject) {
        return INCLUDING_THESE.find(subjectName(subject))
                .orElseThrow(() -> new AssertionError(
                        subject + " is not among what this repository compiled"));
    }

    /** Which of the questions {@code model}'s components hold, in the order it declares them. */
    private static List<String> questionsHeldBy(ClassModel model) {
        List<String> held = new ArrayList<>();
        for (RecordComponentInfo component : componentsOf(model)) {
            if (QUESTIONS.contains(component.descriptor().stringValue())) {
                held.add(component.name().stringValue());
            }
        }
        return held;
    }

    private static List<RecordComponentInfo> componentsOf(ClassModel model) {
        return model.findAttribute(Attributes.record())
                .map(RecordAttribute::components).orElse(List.of());
    }

    /** What {@code model} holds and is built without, said as this reports it. */
    private static List<String> builtWithoutAQuestionIt(ClassModel model) {
        List<RecordComponentInfo> components = componentsOf(model);
        Set<String> refused = refusedBy(canonical(model, components), components);
        List<String> out = new ArrayList<>();
        for (String question : questionsHeldBy(model)) {
            if (!refused.contains(question)) {
                out.add(model.thisClass().asInternalName() + " holds " + question
                        + " and is built without it");
            }
        }
        return out;
    }

    /**
     * The constructor that takes the components, which is the one every other way in goes through.
     *
     * <p>Found by what it takes rather than by being the only one: a carrier may be built by a
     * constructor that fills a component in, and what such a one delegates to is this.
     */
    private static MethodModel canonical(ClassModel model, List<RecordComponentInfo> components) {
        String takes = "(" + components.stream()
                .map(component -> component.descriptor().stringValue())
                .reduce("", String::concat) + ")V";
        for (MethodModel method : model.methods()) {
            if (method.methodName().equalsString("<init>")
                    && method.methodType().equalsString(takes)) {
                return method;
            }
        }
        throw new AssertionError(model.thisClass().asInternalName()
                + " is a record with no constructor over its components, which javac does not make");
    }

    /**
     * Which components {@code made} does not return without.
     *
     * <p>A hand to {@code requireNonNull} is a refusal in itself — the call is what rejects the
     * value, and there is no outcome left to establish. A branch on whether the value is there is
     * not: what the carrier does about the answer is the question, so the way the branch goes when
     * the value is nothing is followed, and it counts where that way cannot come back.
     *
     * <p>Every carrier here is written with a branch, so the {@code requireNonNull} arm is read by
     * nothing in this repository. It is here because the spelling is one this repository uses
     * elsewhere, and it was established by writing one carrier that way and seeing this go on
     * holding — which also found that a refusal given a message loads it between the two.
     */
    private static Set<String> refusedBy(MethodModel made, List<RecordComponentInfo> components) {
        Set<String> refused = new LinkedHashSet<>();
        made.code().ifPresent(code -> {
            List<CodeElement> written = new ArrayList<>();
            Map<Label, Integer> at = new HashMap<>();
            for (CodeElement element : code) {
                if (element instanceof LabelTarget target) {
                    at.put(target.label(), written.size());
                }
                written.add(element);
            }
            // The parameter last read, which is what a decision about one is made of. Kept across
            // whatever is written between the two — the message a refusal is given is loaded there.
            int read = -1;
            for (int i = 0; i < written.size(); i++) {
                switch (written.get(i)) {
                    case LoadInstruction load -> read = load.slot();
                    case BranchInstruction branch -> {
                        Optional<String> component = componentAt(read, components);
                        if (component.isPresent() && nothingComesBackFrom(
                                whereNothingGoes(branch, i, at), written, at)) {
                            refused.add(component.get());
                        }
                        read = -1;
                    }
                    case InvokeInstruction invoked -> {
                        if (invoked.owner().asInternalName().equals("java/util/Objects")
                                && invoked.name().equalsString("requireNonNull")) {
                            componentAt(read, components).ifPresent(refused::add);
                        }
                        read = -1;
                    }
                    default -> { }
                }
            }
        });
        return refused;
    }

    /**
     * Where the branch goes when the value it read is nothing, or nowhere where it is not a branch
     * about that.
     *
     * <p>The two spellings go opposite ways: {@code ifnull} jumps where the value is nothing and
     * {@code ifnonnull} jumps where it is something, so the way this is after is the target of the
     * first and what follows the second.
     */
    private static int whereNothingGoes(BranchInstruction branch, int i, Map<Label, Integer> at) {
        return switch (branch.opcode()) {
            case IFNULL -> at.getOrDefault(branch.target(), -1);
            case IFNONNULL -> i + 1;
            default -> -1;
        };
    }

    /**
     * Whether nothing reachable from {@code from} returns.
     *
     * <p>What a refusal comes to, said as what it rules out: a value the carrier was not handed and
     * a carrier that was built anyway. A throw ends a way and so does the end of the code; anything
     * that returns is the carrier coming back without it.
     */
    private static boolean nothingComesBackFrom(int from, List<CodeElement> written,
                                                Map<Label, Integer> at) {
        if (from < 0) {
            return false;
        }
        Deque<Integer> ways = new ArrayDeque<>(List.of(from));
        Set<Integer> seen = new LinkedHashSet<>();
        while (!ways.isEmpty()) {
            int i = ways.removeFirst();
            if (i >= written.size() || !seen.add(i)) {
                continue;
            }
            if (!(written.get(i) instanceof Instruction instruction)) {
                ways.add(i + 1);
                continue;
            }
            switch (instruction) {
                case ReturnInstruction _ -> {
                    return false;
                }
                case ThrowInstruction _ -> { }
                case BranchInstruction branch -> {
                    ways.add(at.getOrDefault(branch.target(), written.size()));
                    if (branch.opcode() != Opcode.GOTO && branch.opcode() != Opcode.GOTO_W) {
                        ways.add(i + 1);
                    }
                }
                case TableSwitchInstruction table -> {
                    ways.add(at.getOrDefault(table.defaultTarget(), written.size()));
                    table.cases().forEach(
                            one -> ways.add(at.getOrDefault(one.target(), written.size())));
                }
                case LookupSwitchInstruction lookup -> {
                    ways.add(at.getOrDefault(lookup.defaultTarget(), written.size()));
                    lookup.cases().forEach(
                            one -> ways.add(at.getOrDefault(one.target(), written.size())));
                }
                default -> ways.add(i + 1);
            }
        }
        return true;
    }

    /**
     * Which component the local at {@code slot} is, where it is one.
     *
     * <p>Counted the way the frame is laid out — {@code this}, then the components in order, with
     * the wide ones taking two — because that is what a parameter is before it has a name to be
     * read by.
     */
    private static Optional<String> componentAt(int slot, List<RecordComponentInfo> components) {
        int at = 1;
        for (RecordComponentInfo component : components) {
            if (at == slot) {
                return Optional.of(component.name().stringValue());
            }
            String descriptor = component.descriptor().stringValue();
            at += descriptor.equals("J") || descriptor.equals("D") ? 2 : 1;
        }
        return Optional.empty();
    }
}
