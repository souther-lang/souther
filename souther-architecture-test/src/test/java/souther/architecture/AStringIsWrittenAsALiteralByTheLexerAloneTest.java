package souther.architecture;

import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassModel;
import java.lang.classfile.Instruction;
import java.lang.classfile.MethodModel;
import java.lang.classfile.instruction.ConstantInstruction;
import java.lang.classfile.instruction.InvokeDynamicInstruction;
import java.lang.classfile.instruction.InvokeInstruction;
import java.lang.constant.ConstantDesc;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A string is written as a Souther literal by the lexer and by nothing else.
 *
 * <p>Which characters a literal writes with a backslash is the lexer's: it reads them back
 * ({@code CstLexer.textOf}) by the table it refuses an unknown escape by. A writer that spells a
 * literal itself — a value between two quotes — writes {@code a"b} as {@code "a"b"}, which reads back
 * as another string or does not read at all, and it does so the day a value holds a quote and not
 * before. So the writing is {@code CstLexer.literalOf}, the other direction of the same table, and a
 * hand-built one anywhere else is refused here rather than found in a report.
 *
 * <p>Not only Souther's. A value written into a call a reader is told to send is a JSON string, and
 * spelling one by hand fails the same way; that one is written by the writer that puts the
 * documentation server's answers on the wire. Either way a value between two quotes is somebody's
 * writer and not a concatenation.
 *
 * <p>Read off the compiled classes of what this repository publishes. A string concatenation is a
 * recipe whose argument slots are {@code \u0001} and whose constants are {@code \u0002}; a slot
 * between two quotes is a literal spelled by hand. A {@code StringBuilder} handed a quote character
 * is the same thing written the long way.
 */
class AStringIsWrittenAsALiteralByTheLexerAloneTest {

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    /** The one writer of a literal, which the rule is about everyone but. */
    private static final String THE_LEXER = "souther/compiler/cst/CstLexer#literalOf";

    private static final String CONCATENATION = "java/lang/invoke/StringConcatFactory";

    private static final Set<String> BUILDERS =
            Set.of("java/lang/StringBuilder", "java/lang/StringBuffer");

    @Test
    void noWriterButTheLexerPutsAValueBetweenTwoQuotes() {
        assertEquals(List.of(), spellingALiteral(),
                "a literal spelled by hand writes a value holding a quote, a backslash or a line"
                        + " break as source that reads back as something else; write it with"
                        + " CstLexer.literalOf");
    }

    /** The control: the lexer's own writer is read by the same walk, and it does hand a builder a
     *  quote. Without it the assertion above would hold of a walk that read nothing. */
    @Test
    void theLexersWriterIsSeenByTheSameWalk() {
        assertTrue(spelling(false).contains(THE_LEXER),
                () -> "the walk did not see " + THE_LEXER + " hand a builder a quote");
    }

    private static List<String> spellingALiteral() {
        return spelling(true);
    }

    /** Every member that spells a literal by hand, the lexer's writer left out where
     *  {@code butTheLexer} says so. */
    private static List<String> spelling(boolean butTheLexer) {
        TreeSet<String> out = new TreeSet<>();
        for (ClassModel owner : COMPILED.all()) {
            String name = owner.thisClass().asInternalName();
            for (MethodModel method : owner.methods()) {
                String member = name + "#" + method.methodName().stringValue();
                if (butTheLexer && member.equals(THE_LEXER)) {
                    continue;
                }
                List<Instruction> code = instructionsOf(method);
                for (int i = 0; i < code.size(); i++) {
                    if (betweenQuotes(code.get(i))
                            || (i > 0 && aQuote(code.get(i - 1)) && appended(code.get(i)))) {
                        out.add(member);
                    }
                }
            }
        }
        return new ArrayList<>(out);
    }

    /** Whether {@code instruction} concatenates a value between two quotes. */
    private static boolean betweenQuotes(Instruction instruction) {
        if (!(instruction instanceof InvokeDynamicInstruction dynamic)
                || !CONCATENATION.equals(dynamic.invokedynamic().bootstrap().bootstrapMethod()
                        .reference().owner().name().stringValue())) {
            return false;
        }
        for (ConstantDesc argument : dynamic.bootstrapArgs()) {
            if (argument instanceof String recipe
                    && (recipe.contains("\"\u0001\"") || recipe.contains("\"\u0002\""))) {
                return true;
            }
        }
        return false;
    }

    /** Whether {@code instruction} pushes the quote character. */
    private static boolean aQuote(Instruction instruction) {
        return instruction instanceof ConstantInstruction constant
                && (Integer.valueOf('"').equals(constant.constantValue())
                        || "\"".equals(constant.constantValue()));
    }

    /** Whether {@code instruction} appends to a builder. */
    private static boolean appended(Instruction instruction) {
        return instruction instanceof InvokeInstruction call
                && BUILDERS.contains(call.owner().asInternalName())
                && call.name().equalsString("append");
    }

    private static List<Instruction> instructionsOf(MethodModel method) {
        return method.code().map(code -> code.elementList().stream()
                .filter(Instruction.class::isInstance)
                .map(Instruction.class::cast)
                .toList()).orElse(List.of());
    }
}
