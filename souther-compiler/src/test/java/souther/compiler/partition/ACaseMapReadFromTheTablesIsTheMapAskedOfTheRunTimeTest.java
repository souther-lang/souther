package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.evaluate.BoundUnderEvaluation;
import souther.compiler.regex.CodeMap;
import souther.compiler.semantics.CaseMapping;

import java.util.function.UnaryOperator;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The map a case conversion is on code points does not ask the run time of the code points the
 * conversion's tables say it leaves as they are everywhere. It is the map worked out by asking the
 * run time of every code point: for each conversion, and for one made of the two, where what it
 * leaves alone is what each of its conversions does.
 */
class ACaseMapReadFromTheTablesIsTheMapAskedOfTheRunTimeTest {

    private static void same(CaseMapping mapping) {
        UnaryOperator<String> conversion = text -> BoundUnderEvaluation.mapped(mapping, text);
        assertEquals(CodeMap.of(conversion),
                CodeMap.of(conversion, CaseMaps.leftAloneEverywhere(mapping)), mapping::toString);
    }

    @Test
    void lowercase() {
        same(CaseMapping.LOWERCASE);
    }

    @Test
    void uppercase() {
        same(CaseMapping.UPPERCASE);
    }

    @Test
    void lowercaseOfUppercase() {
        same(new CaseMapping.Lowercase(CaseMapping.UPPERCASE));
    }
}
