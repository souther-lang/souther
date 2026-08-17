package souther.compiler.meta;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.lang.classfile.ClassFile;
import java.lang.classfile.ClassModel;
import java.lang.classfile.CodeModel;
import java.lang.classfile.instruction.InvokeInstruction;
import java.lang.classfile.instruction.NewObjectInstruction;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * What decides a policy reads the answer; what writes a sentence writes one payload's words; and
 * what makes an answer is the reading that made it.
 *
 * <p>{@code Reachability} has three arms and each carries something: why nothing arrives, what says
 * something does, why nothing settled it. A reader that took one of those apart would be deciding
 * an obligation, a diagnostic or a claim on a distinction inside the payload — and a distinction
 * added there later would silently become a change to that decision.
 *
 * <p><b>Read off the compiled classes.</b> The arms being package-private stops the
 * {@code instanceof} and nothing else: {@code Words} and the factories are public, so a static
 * import or a qualified call reaches them, and a scan over source text answers about spellings
 * rather than about what a class does. What is checked here is what the bytecode says — who calls
 * {@code said}, who implements a {@code Words}, who calls a factory, and whose code runs an
 * answer's constructor — which no way of writing the call can dress up as something else.
 *
 * <p>Both directions are asserted. A check that only counts violations passes when it reads nothing
 * at all, so every rule below also names what it expects to find and fails where that is missing.
 */
class OnlyARendererTakesAProofApartTest {

    private static final String REACH = "souther.compiler.reach.";

    /** Who may ask a payload what it says, and write the words it says it in. */
    private static final Map<String, String> WRITES_THE_WORDS_OF = Map.of(
            REACH + "Proof", "souther.compiler.query.Adequacy$DeadBranches$DeadBranchProofWords",
            REACH + "WhyUnsettled", "souther.compiler.query.ClaimAnnotations$UnsettledWords");

    /**
     * Who may make an answer.
     *
     * <p>By nest rather than by class: the reading is written as a class with helpers inside it,
     * and which of them holds a given construction is its own business. What matters is that
     * nothing outside the reading makes one.
     */
    private static final String THE_READING = "souther.compiler.check.PathReachability";

    /** The answers themselves, whose constructors are as good as a factory to a consumer. */
    private static final List<String> ANSWERS = List.of(
            REACH + "Reachability$Unreachable",
            REACH + "Reachability$Reachable",
            REACH + "Reachability$Unsettled");

    /** One compiled call or construction, and the class whose code holds it. */
    private record Use(String from, String owner, String member, boolean isStatic) {}

    @Test
    void onlyItsOwnWordsAskAPayloadWhatItSays() throws IOException {
        Map<String, List<String>> asked = new LinkedHashMap<>();
        for (Use use : uses()) {
            if (WRITES_THE_WORDS_OF.containsKey(use.owner()) && use.member().equals("said")) {
                asked.computeIfAbsent(use.owner(), _ -> new ArrayList<>()).add(use.from());
            }
        }
        WRITES_THE_WORDS_OF.forEach((payload, words) -> {
            List<String> callers = asked.getOrDefault(payload, List.of()).stream().distinct()
                    .toList();
            assertFalse(callers.isEmpty(), payload + " is asked what it says by nothing at all;"
                    + " this check is reading no calls");
            assertEquals(List.of(words), callers,
                    payload + " is asked what it says by something that is not its words");
        });
    }

    @Test
    void andOnlyThoseWordsAreWritten() throws IOException {
        Map<String, List<String>> implementors = new LinkedHashMap<>();
        for (Path each : classes()) {
            ClassModel model = ClassFile.of().parse(Files.readAllBytes(each));
            for (var face : model.interfaces()) {
                String name = face.asInternalName().replace('/', '.');
                WRITES_THE_WORDS_OF.forEach((payload, words) -> {
                    if (name.equals(payload + "$Words")) {
                        implementors.computeIfAbsent(payload, _ -> new ArrayList<>())
                                .add(model.thisClass().asInternalName().replace('/', '.'));
                    }
                });
            }
        }
        WRITES_THE_WORDS_OF.forEach((payload, words) -> assertEquals(List.of(words),
                implementors.getOrDefault(payload, List.of()),
                payload + "'s words are written somewhere other than by its own renderer"));
    }

    @Test
    void andNothingButTheReadingMakesAnAnswer() throws IOException {
        List<String> outside = new ArrayList<>();
        List<Use> made = new ArrayList<>();
        boolean sawAConstructor = false;
        for (Use use : uses()) {
            // A factory is static; reading a component off an answer already in hand is not one,
            // and is what a policy consumer does when it passes a reason along.
            boolean isFactory = use.owner().startsWith(REACH) && use.isStatic();
            boolean isAnswer = ANSWERS.contains(use.owner()) && use.member().equals("<init>");
            if (!isFactory && !isAnswer) {
                continue;
            }
            sawAConstructor |= isAnswer;
            made.add(use);
            if (!nestOf(use.from()).equals(THE_READING)) {
                outside.add(use.from() + " -> " + use.owner() + "." + use.member());
            }
        }
        assertFalse(made.isEmpty(), "nothing makes an answer at all; this check is reading nothing");
        assertFalse(!sawAConstructor,
                "no answer's constructor was seen; the check would miss one built directly");
        assertEquals(List.of(), outside, "these make an answer the reading did not make");
    }

    /** The nest a class belongs to: what is written inside the reading is the reading. */
    private static String nestOf(String binaryName) {
        int nested = binaryName.indexOf('$');
        return nested < 0 ? binaryName : binaryName.substring(0, nested);
    }

    /** Every call and construction the compiled classes hold, the answers' own aside. */
    private static List<Use> uses() throws IOException {
        List<Use> found = new ArrayList<>();
        for (Path each : classes()) {
            ClassModel model = ClassFile.of().parse(Files.readAllBytes(each));
            String from = model.thisClass().asInternalName().replace('/', '.');
            if (from.startsWith(REACH)) {
                continue;   // what the answers do among themselves is their own business
            }
            for (var method : model.methods()) {
                CodeModel code = method.code().orElse(null);
                if (code == null) {
                    continue;
                }
                for (var element : code) {
                    if (element instanceof InvokeInstruction call) {
                        found.add(new Use(from, call.owner().asInternalName().replace('/', '.'),
                                call.name().stringValue(),
                                call.opcode() == java.lang.classfile.Opcode.INVOKESTATIC));
                    } else if (element instanceof NewObjectInstruction made) {
                        found.add(new Use(from,
                                made.className().asInternalName().replace('/', '.'), "<init>",
                                false));
                    }
                }
            }
        }
        assertFalse(found.isEmpty(), "no compiled call was read at all");
        return found;
    }

    /** The compiled main classes of this module. Read from the build rather than from the sources,
     *  because what a call is, is what the compiler made of it. */
    private static List<Path> classes() throws IOException {
        Path root = Path.of("target", "classes").toAbsolutePath();
        try (Stream<Path> walk = Files.walk(root)) {
            return walk.filter(each -> each.toString().endsWith(".class")).toList();
        }
    }
}
