package souther.compiler;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.lang.classfile.ClassFile;
import java.lang.classfile.ClassModel;
import java.lang.classfile.CodeElement;
import java.lang.classfile.CodeModel;
import java.lang.classfile.Instruction;
import java.lang.classfile.Label;
import java.lang.classfile.MethodModel;
import java.lang.classfile.Opcode;
import java.lang.classfile.instruction.BranchInstruction;
import java.lang.classfile.instruction.ExceptionCatch;
import java.lang.classfile.instruction.LabelTarget;
import java.lang.classfile.instruction.LookupSwitchInstruction;
import java.lang.classfile.instruction.ReturnInstruction;
import java.lang.classfile.instruction.SwitchCase;
import java.lang.classfile.instruction.TableSwitchInstruction;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * In the packages that read a program, no failure nobody named comes back as an answer.
 *
 * <p>What an analysis may be quiet about is a limit it named, and a limit is a value something with
 * the standing to say so made. A failure with no such value behind it is this compiler contradicting
 * itself, and the way that goes wrong is silent: a subject the analysis fell over on comes back with
 * nothing to report, which is what a subject that passed comes back as. Nothing fails while it does,
 * which is why a person reading the diff will not find it either.
 *
 * <p><b>What is watched is the way out of a handler, not the catch.</b> Catching widely is ordinary
 * and sometimes the only thing on offer — a class file the JDK refuses to parse, a message the
 * formatter will not take — and the ones in these packages today all end by throwing: the emitter
 * says what it could not read back, the writer says which limit of the class file was reached, a
 * term says which of the values it holds did not answer. None of those turns a failure into an
 * answer. What does is a handler a caller can return through, so that is what this asks: from where
 * the handler begins, following only the edges an ordinary run takes, is there a {@code return} to
 * arrive at.
 *
 * <p>So it is not "a broad catch is refused", which would be false of every one of them, and it is
 * not a list of the places allowed to swallow, which would be a copy of the code kept somewhere
 * else. It is the three packages and the one question.
 *
 * <p>Read off the compiled classes, because what a handler does is a fact about the bytecode. A
 * {@code throw} of a value some other method computed is an {@code athrow} here like any other, and
 * a handler that branches before deciding is walked rather than read off its first instruction.
 *
 * <p><b>Most of what is examined is not written down anywhere.</b> A {@code switch} over a sealed
 * type compiles to a handler catching {@link Throwable} and rethrowing it as a
 * {@link MatchException}, and this compiler is written in those, so they outnumber the handlers a
 * person typed many times over. They are left in rather than recognised: telling them apart means
 * knowing how one version of javac writes them, and there is nothing to be had by it — every one of
 * them ends by throwing, which is the answer this asks for. What it costs is that the population
 * being non-empty no longer says much on its own, which is what the second test below is for.
 */
class NoBroadFailureBecomesAnAnswerInTheAnalysisCoreTest {

    /**
     * Where a program is read.
     *
     * <p>Not every package of this compiler. A run has to be able to go on from things that are not
     * about a program at all — a jar it cannot parse, a document it cannot format, an editor session
     * outliving a request — and those adapters answer with what they had before. These three are
     * where a program is turned into what is said about it, and there an answer that came out of a
     * failure is indistinguishable from an answer.
     */
    private static final Set<String> READ_A_PROGRAM = Set.of(
            "souther/compiler/check/",
            "souther/compiler/codegen/",
            "souther/compiler/query/");

    /**
     * What counts as wide.
     *
     * <p>Unchecked types of the JDK that this compiler gave no meaning to, so a handler naming one
     * of them says nothing about what it met. A refusal this compiler declares is not here however
     * many methods raise it: catching {@code NotOneClause} is catching one thing.
     */
    private static final Set<String> WIDE = Set.of(
            "java/lang/Throwable",
            "java/lang/Exception",
            "java/lang/RuntimeException",
            "java/lang/IllegalStateException",
            "java/lang/IllegalArgumentException");

    /** A handler, where it is, and what it catches. */
    private record Handler(String where, String catches) implements Comparable<Handler> {

        @Override
        public String toString() {
            return where + " catches " + catches;
        }

        @Override
        public int compareTo(Handler other) {
            return toString().compareTo(other.toString());
        }
    }

    private record Scan(Set<Handler> examined, Set<Handler> reachingAReturn) {}

    @Test
    void noWideHandlerInThemCanReturn() throws IOException {
        Scan scan = scan();

        assertEquals(Set.of(), scan.reachingAReturn(),
                "a run through one of these leaves a handler and goes on to answer, so a failure"
                        + " nobody named a limit comes back as what this compiler has to say about"
                        + " the program. What may be quiet is a limit something made, and there is"
                        + " no value behind these");
    }

    /**
     * And the handlers somebody wrote are among them.
     *
     * <p>Without this the question above is answered by a walk that read nothing — a package renamed,
     * a directory not built, a way of writing a handler the reader does not recognise — or by one
     * that read only what javac put there. A handler naming anything but {@link Throwable} is one
     * somebody typed, since the wrapper a pattern switch compiles to always names that; so this says
     * the walk reached the code rather than only its desugaring.
     */
    @Test
    void theHandlersSomebodyWroteAreAmongThem() throws IOException {
        assertTrue(scan().examined().stream()
                        .anyMatch(handler -> !handler.catches().equals("Throwable")),
                "every wide handler found names Throwable, which is what a pattern switch compiles"
                        + " to — so this walk reached the desugaring and not the code, and the"
                        + " check above passed over nothing anybody wrote");
    }

    private static Scan scan() throws IOException {
        Set<Handler> examined = new TreeSet<>();
        Set<Handler> returning = new TreeSet<>();
        for (Path each : classes()) {
            ClassModel model = ClassFile.of().parse(Files.readAllBytes(each));
            String owner = model.thisClass().asInternalName();
            if (READ_A_PROGRAM.stream().noneMatch(owner::startsWith)) {
                continue;
            }
            for (MethodModel method : model.methods()) {
                method.code().ifPresent(code -> {
                    Walk walk = Walk.of(code);
                    for (ExceptionCatch caught : code.exceptionHandlers()) {
                        String type = caught.catchType()
                                .map(entry -> entry.asInternalName()).orElse(null);
                        if (type == null || !WIDE.contains(type)) {
                            continue;
                        }
                        Handler handler = new Handler(
                                owner.replace('/', '.') + "." + method.methodName().stringValue(),
                                type.substring(type.lastIndexOf('/') + 1));
                        examined.add(handler);
                        if (walk.canReturnFrom(caught.handler())) {
                            returning.add(handler);
                        }
                    }
                });
            }
        }
        return new Scan(examined, returning);
    }

    /**
     * One method's instructions and the edges an ordinary run takes between them.
     *
     * <p>Exception edges are left out on purpose. A handler reached from inside another handler is
     * itself one of the handlers this asks about, so following the throw would answer for it twice
     * and would say of a handler that rethrows that it can return.
     */
    private record Walk(List<Instruction> instructions, Map<Label, Integer> at) {

        static Walk of(CodeModel code) {
            List<Instruction> instructions = new ArrayList<>();
            Map<Label, Integer> at = new IdentityHashMap<>();
            for (CodeElement element : code) {
                if (element instanceof LabelTarget target) {
                    at.put(target.label(), instructions.size());
                } else if (element instanceof Instruction instruction) {
                    instructions.add(instruction);
                }
            }
            return new Walk(instructions, at);
        }

        boolean canReturnFrom(Label handler) {
            Integer start = at.get(handler);
            if (start == null) {
                return false;
            }
            Set<Integer> seen = new HashSet<>();
            Deque<Integer> todo = new ArrayDeque<>();
            todo.add(start);
            while (!todo.isEmpty()) {
                int here = todo.removeFirst();
                if (here >= instructions.size() || !seen.add(here)) {
                    continue;
                }
                Instruction instruction = instructions.get(here);
                if (instruction instanceof ReturnInstruction) {
                    return true;
                }
                todo.addAll(nextAfter(here, instruction));
            }
            return false;
        }

        private List<Integer> nextAfter(int here, Instruction instruction) {
            List<Integer> out = new ArrayList<>();
            switch (instruction) {
                case BranchInstruction branch -> {
                    add(out, branch.target());
                    if (branch.opcode() != Opcode.GOTO && branch.opcode() != Opcode.GOTO_W) {
                        out.add(here + 1);
                    }
                }
                case TableSwitchInstruction table -> {
                    add(out, table.defaultTarget());
                    for (SwitchCase one : table.cases()) {
                        add(out, one.target());
                    }
                }
                case LookupSwitchInstruction lookup -> {
                    add(out, lookup.defaultTarget());
                    for (SwitchCase one : lookup.cases()) {
                        add(out, one.target());
                    }
                }
                default -> {
                    // athrow ends a way out and has no ordinary successor; a return was answered
                    // above. Everything else falls through to what is written after it.
                    if (instruction.opcode() != Opcode.ATHROW) {
                        out.add(here + 1);
                    }
                }
            }
            return out;
        }

        private void add(List<Integer> out, Label label) {
            Integer target = at.get(label);
            if (target != null) {
                out.add(target);
            }
        }
    }

    private static List<Path> classes() throws IOException {
        Path root = Path.of("target", "classes").toAbsolutePath();
        try (Stream<Path> walk = Files.walk(root)) {
            List<Path> found = new ArrayList<>(
                    walk.filter(p -> p.toString().endsWith(".class")).toList());
            assertFalse(found.isEmpty(), "no compiled class was read at all, so this says nothing");
            return found;
        }
    }
}
