package souther.architecture;

import java.lang.classfile.ClassModel;
import java.lang.classfile.CodeElement;
import java.lang.classfile.CodeModel;
import java.lang.classfile.MethodModel;
import java.lang.classfile.instruction.InvokeInstruction;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Every call, in a population of compiled classes, to a {@code java.math.BigDecimal} member that
 * is not known to answer on every value — the ones {@link #ANSWERS_ON_EVERY_VALUE} names are left
 * out, since no refusal there ever needs explaining.
 *
 * <p>A row's identity is the caller ({@link AMethod}, so an overloaded caller keeps its own row)
 * and the member it calls, together with which occurrence of that same call inside that same
 * method this is — not a bytecode offset, which an unrelated edit moves without the call itself
 * changing, but a count that moves only when the number of times the method makes that call does.
 * Two identical calls inside one method are two rows, and removing the first shifts the second's
 * occurrence down: the row that goes is the one whose caller stopped, not one that happened to keep
 * a permission that was never its own to begin with.
 *
 * <p>What may be listed as a reason nobody looked at, versus one this repository is written down as
 * standing by, is for the check that calls this to decide; this only says where the calls are.
 */
final class BigDecimalCalls {

    private static final String OWNER = "java/math/BigDecimal";

    /** The members every {@code BigDecimal} answers on, whatever the value it is asked of: its sign,
     *  scale, precision and digits, a comparison, a negation, the greater or the lesser of two, and
     *  a narrowing {@code Number} conversion that loses precision rather than refusing it. Checked
     *  against the JDK rather than assumed — {@code movePointLeft}/{@code Right} looked the same
     *  shape as these and refuses where the moved scale leaves the range an {@code int} holds, so it
     *  is not one of them. Not a question here. */
    static final Set<String> ANSWERS_ON_EVERY_VALUE = Set.of(
            "compareTo(Ljava/math/BigDecimal;)I",
            "equals(Ljava/lang/Object;)Z",
            "hashCode()I",
            "toString()Ljava/lang/String;",
            "signum()I",
            "scale()I",
            "precision()I",
            "unscaledValue()Ljava/math/BigInteger;",
            "negate()Ljava/math/BigDecimal;",
            "abs()Ljava/math/BigDecimal;",
            "max(Ljava/math/BigDecimal;)Ljava/math/BigDecimal;",
            "min(Ljava/math/BigDecimal;)Ljava/math/BigDecimal;",
            "intValue()I",
            "longValue()J",
            "valueOf(J)Ljava/math/BigDecimal;",
            "valueOf(JI)Ljava/math/BigDecimal;",
            "<init>(Ljava/math/BigInteger;)V",
            "<init>(Ljava/math/BigInteger;I)V");

    private BigDecimalCalls() {}

    /** One call, at one occurrence inside its caller, to a member that can refuse. */
    record Call(String caller, String member, int occurrence) {

        /** The row a check names this call by: the occurrence only where there is more than one,
         *  since a single call needs no count to tell it apart from itself. */
        String row() {
            return caller + " " + member + (occurrence == 1 ? "" : " #" + occurrence);
        }
    }

    /** Every such call inside {@code classes}, one entry per invocation and none collapsed into
     *  another that happens to read the same. */
    static List<Call> in(Iterable<ClassModel> classes) {
        List<Call> out = new ArrayList<>();
        for (ClassModel owner : classes) {
            for (MethodModel method : owner.methods()) {
                Map<String, Integer> seenInThisMethod = new HashMap<>();
                for (CodeModel code : method.code().stream().toList()) {
                    for (CodeElement element : code) {
                        if (element instanceof InvokeInstruction invoke
                                && invoke.owner().asInternalName().equals(OWNER)) {
                            String member = invoke.name().stringValue() + invoke.type().stringValue();
                            if (!ANSWERS_ON_EVERY_VALUE.contains(member)) {
                                int occurrence = seenInThisMethod.merge(member, 1, Integer::sum);
                                out.add(new Call(AMethod.of(owner, method), member, occurrence));
                            }
                        }
                    }
                }
            }
        }
        return out;
    }
}
