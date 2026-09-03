package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.query.ReadAs;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A position and the same position under a name are proposed for alike.
 *
 * <p>Two routes reach one answer. A position whose type is written as a primitive is answered from
 * what the primitive is; a position wearing a name is asked what it divides into first, and a
 * {@code Bool} divides into two and an {@code Option} into present and absent. So the value a row
 * carries at {@code Bool} is chosen by one reading and the value it carries at {@code data F = Bool}
 * by another, and nothing says the two agree.
 *
 * <p>Held because they have to. A name is how a value is written and never what it is, so a name put
 * on a position cannot change which value stands for it. What is pinned here is that the two routes
 * arrive at the same value today, which is what makes joining them a change that keeps the answers
 * rather than one that quietly picks a different row.
 */
class APositionIsProposedForAlikeWhetherOrNotItWearsANameTest {

    private static final RuleReadingSource RULES = RuleReadings.ofSource("""
            module demo

            data F = Bool

            data O = Option<String>
            """);

    private static List<String> proposedFor(Type type) {
        return Partitions.representativesOf(type, RULES, ReadAs.THE_COMPILATION_DOES, null, Set.of())
                .stream().map(FixtureTemplate::text).toList();
    }

    private static Type named(String type) {
        return Type.ref(TypeSymbols.declared(new TypeKey(RULES.symbols().module(), type)));
    }

    /** A flag, which the type divides into two: the same one of them either way. */
    @Test
    void aFlagIsProposedForAlikeUnderANameAndWithoutOne() {
        assertEquals(List.of("true"), proposedFor(Type.BOOL));
        assertEquals(List.of("F(true)"), proposedFor(named("F")));
    }

    /** An option, which divides into absent and present: the same one of them either way. */
    @Test
    void anOptionIsProposedForAlikeUnderANameAndWithoutOne() {
        assertEquals(List.of("None"), proposedFor(Type.option(Type.STRING)));
        assertEquals(List.of("O(None)"), proposedFor(named("O")));
    }
}
