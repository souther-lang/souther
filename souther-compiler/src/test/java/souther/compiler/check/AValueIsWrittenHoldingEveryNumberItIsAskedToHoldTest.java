package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.TestDay;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A value of a record is shown to hold some numbers only where every one of them is in the value
 * written down: a number asked at a place the value has none of is a number it was not shown to
 * hold, and it is not left out.
 */
class AValueIsWrittenHoldingEveryNumberItIsAskedToHoldTest {

    private static final FieldDomains IN = readingOf();

    private static FieldDomains readingOf() {
        Compilation compilation = ACompiledModel.refusedWith(List.of(), Compilation.ofSource("""
                module example.pairs

                data Pair = { e: Int, p: Int }
                    invariant eInRange = e >= 1 && e <= 12
                    invariant tied = p == e - 1
                """, "Main"));
        String module = compilation.modules().get(0);
        TypeSymbol.AtModule named = TypeSymbols.declared(new TypeKey(module, "Pair"));
        return FieldDomains.of(named, RuleReadingContext.unshared(
                RuleReadings.of(compilation, module), ReadAs.THE_COMPILATION_DOES,
                TestDay.TODAY));
    }

    @Test
    void aNumberTheClausesLeaveAtItsPlaceIsHeld() {
        assertTrue(IN.holdsAValueWith(Map.of(RuleKey.of("p"), 0L, RuleKey.of("e"), 1L)));
    }

    @Test
    void aNumberTheClausesRefuseBesideAnotherIsNotHeld() {
        assertFalse(IN.holdsAValueWith(Map.of(RuleKey.of("p"), 0L, RuleKey.of("e"), 2L)));
    }

    @Test
    void aNumberAtAPlaceTheRecordHasNoneOfIsNotHeld() {
        assertFalse(IN.holdsAValueWith(Map.of(RuleKey.of("p"), 0L, RuleKey.of("missing"), 0L)));
    }
}
