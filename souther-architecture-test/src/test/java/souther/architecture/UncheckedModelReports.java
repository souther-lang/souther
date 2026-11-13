package souther.architecture;

import java.lang.classfile.ClassModel;
import java.lang.classfile.CodeElement;
import java.lang.classfile.CodeModel;
import java.lang.classfile.MethodModel;
import java.lang.classfile.Opcode;
import java.lang.classfile.PseudoInstruction;
import java.lang.classfile.instruction.InvokeInstruction;
import java.lang.classfile.instruction.StackInstruction;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Stream;

/**
 * The methods of some test classes that read the report of a model they never asked compiles.
 *
 * <p>A method is refused when it gets a model it did not ask about and reads a report of it. It
 * gets one by making it from a source, or by calling a method of its own class that returns one
 * made and not asked about. It reads a report by calling what reads one, or a method of its own
 * class that does, which is how a model comes to be made in one method and read in another.
 *
 * <p>Asking is a look at {@code errors()} whose answer is used, a call to the helper that stops
 * the test on an error, or a call to a method of its own class that does either. An {@code errors()} whose answer is dropped is not a look. What this cannot
 * see is a model handed in from another class, which is asked about where it was made, and a model
 * asked about and then replaced by another.
 */
final class UncheckedModelReports {

    private static final String COMPILATION = "souther/compiler/query/Compilation";

    private static final String REPORT = "souther/compiler/report/AdequacyReport";

    private final String helper;

    /** @param helper the class a test goes through to have a model held to compile */
    UncheckedModelReports(String helper) {
        this.helper = helper;
    }

    /** The refused methods of {@code classes}, as {@link AMethod} says them. */
    Set<String> in(Collection<ClassModel> classes) {
        Set<String> refused = new TreeSet<>();
        for (ClassModel each : classes) {
            Map<String, List<CodeElement>> bodies = bodiesOf(each);
            Set<String> askers = asking(each, bodies);
            Set<String> unasked = makingAModelNobodyAsksAbout(each, bodies, askers);
            Set<String> reading = reading(each, bodies);
            for (MethodModel method : each.methods()) {
                List<CodeElement> body = bodies.get(key(method));
                if (body != null && !asks(each, body, askers)
                        && gets(each, body, unasked) && reads(each, body, reading)) {
                    refused.add(AMethod.of(each, method));
                }
            }
        }
        return refused;
    }

    /** How many methods of {@code classes} make a model, ask about it and read a report of it. */
    int asking(Collection<ClassModel> classes) {
        int asked = 0;
        for (ClassModel each : classes) {
            Map<String, List<CodeElement>> bodies = bodiesOf(each);
            Set<String> askers = asking(each, bodies);
            for (List<CodeElement> body : bodies.values()) {
                boolean makes = body.stream().anyMatch(
                        element -> element instanceof InvokeInstruction call && makes(call));
                if (makes && asks(each, body, askers) && reads(each, body, Set.of())) {
                    asked++;
                }
            }
        }
        return asked;
    }

    private static Map<String, List<CodeElement>> bodiesOf(ClassModel each) {
        Map<String, List<CodeElement>> bodies = new LinkedHashMap<>();
        for (MethodModel method : each.methods()) {
            CodeModel code = method.code().orElse(null);
            if (code != null) {
                bodies.put(key(method), code.elementList());
            }
        }
        return bodies;
    }

    private static String key(MethodModel method) {
        return method.methodName().stringValue() + method.methodTypeSymbol().descriptorString();
    }

    /** The methods of {@code each} returning a model they got and never asked about. */
    private Set<String> makingAModelNobodyAsksAbout(ClassModel each,
                                                    Map<String, List<CodeElement>> bodies,
                                                    Set<String> askers) {
        Set<String> unasked = new LinkedHashSet<>();
        boolean grew = true;
        while (grew) {
            grew = false;
            for (MethodModel method : each.methods()) {
                List<CodeElement> body = bodies.get(key(method));
                if (body != null
                        && method.methodTypeSymbol().returnType().descriptorString()
                                .equals("L" + COMPILATION + ";")
                        && !asks(each, body, askers) && gets(each, body, unasked)) {
                    grew |= unasked.add(key(method));
                }
            }
        }
        return unasked;
    }

    /** The methods of {@code each} that read a report, directly or through one that does. */
    private Set<String> reading(ClassModel each, Map<String, List<CodeElement>> bodies) {
        Set<String> reading = new LinkedHashSet<>();
        boolean grew = true;
        while (grew) {
            grew = false;
            for (Map.Entry<String, List<CodeElement>> body : bodies.entrySet()) {
                if (!reading.contains(body.getKey()) && reads(each, body.getValue(), reading)) {
                    reading.add(body.getKey());
                    grew = true;
                }
            }
        }
        return reading;
    }

    private boolean gets(ClassModel each, List<CodeElement> body, Set<String> unasked) {
        return calls(body).anyMatch(call -> makes(call)
                || (owns(each, call) && unasked.contains(key(call))));
    }

    private boolean reads(ClassModel each, List<CodeElement> body, Set<String> reading) {
        return calls(body).anyMatch(call -> readsAReport(call)
                || (owns(each, call) && reading.contains(key(call))));
    }

    /** The methods of {@code each} that ask, directly or through a method of the class that does. */
    private Set<String> asking(ClassModel each, Map<String, List<CodeElement>> bodies) {
        Set<String> askers = new LinkedHashSet<>();
        boolean grew = true;
        while (grew) {
            grew = false;
            for (Map.Entry<String, List<CodeElement>> body : bodies.entrySet()) {
                if (!askers.contains(body.getKey()) && asks(each, body.getValue(), askers)) {
                    askers.add(body.getKey());
                    grew = true;
                }
            }
        }
        return askers;
    }

    private boolean asks(ClassModel each, List<CodeElement> body, Set<String> askers) {
        if (calls(body).anyMatch(call -> owns(each, call) && askers.contains(key(call)))) {
            return true;
        }
        for (int i = 0; i < body.size(); i++) {
            if (!(body.get(i) instanceof InvokeInstruction call)) {
                continue;
            }
            if (owner(call).equals(helper)) {
                return true;
            }
            if (COMPILATION.equals(owner(call)) && Set.of("errors", "failure", "structuralFailure")
                    .contains(call.name().stringValue()) && !dropped(body, i)) {
                return true;
            }
        }
        return false;
    }

    /** Whether what the call at {@code at} answered is popped off the stack unread. */
    private static boolean dropped(List<CodeElement> body, int at) {
        for (int i = at + 1; i < body.size(); i++) {
            if (!(body.get(i) instanceof PseudoInstruction)) {
                return body.get(i) instanceof StackInstruction it && it.opcode() == Opcode.POP;
            }
        }
        return false;
    }

    private static boolean makes(InvokeInstruction call) {
        return COMPILATION.equals(owner(call)) && call.name().stringValue().startsWith("of");
    }

    private static boolean readsAReport(InvokeInstruction call) {
        return (REPORT.equals(owner(call)) && call.name().stringValue().equals("of"))
                || (COMPILATION.equals(owner(call))
                        && Set.of("db", "adequacy").contains(call.name().stringValue()));
    }

    private static Stream<InvokeInstruction> calls(List<CodeElement> body) {
        return body.stream().filter(InvokeInstruction.class::isInstance)
                .map(InvokeInstruction.class::cast);
    }

    private static boolean owns(ClassModel each, InvokeInstruction call) {
        return owner(call).equals(each.thisClass().asInternalName());
    }

    private static String owner(InvokeInstruction call) {
        return call.owner().asInternalName();
    }

    private static String key(InvokeInstruction call) {
        return call.name().stringValue() + call.type().stringValue();
    }
}
