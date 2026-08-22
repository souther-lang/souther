package souther.compiler.coverage;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Compilation;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Only a declaration can be handed a rule, which is what lets a fork name the one that owns it.
 *
 * <p>Who decides at a fork is read off the declaration that wrote it, and which copy of that
 * declaration the fork stands in is what says which rule arrived. Both rest on one thing about the
 * language: a value of function type reaches a body only through a parameter some declaration wrote
 * down. A block becomes a function value where a function type is expected, and the only thing that
 * expects one is a declared parameter.
 *
 * <p>So a name a body binds a block to takes no rule. That is why a fork inside one is the
 * declaration's own however many times the body calls it, and why nothing here has to say what a
 * rule handed to such a name would mean.
 *
 * <p>Written down because the reading depends on it and cannot see it. The day a body can hand a
 * rule to something it bound itself, a fork inside that something rests on a rule this reading does
 * not know is one — and every call of it would be counted as one arm to cover, which is the answer
 * this whole measure exists to refuse. This turns that day into a red test rather than a quiet
 * number.
 */
class OnlyADeclarationCanBeHandedARuleTest {

    private static List<String> refused(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.answerEverything();
        return compilation.diagnostics().values().stream().flatMap(List::stream)
                .map(each -> String.valueOf(each.diagnostic().code())).toList();
    }

    /** A rule handed to a name the body bound a block to. */
    @Test
    void aBlockBoundByALetTakesNoRule() {
        assertEquals(List.of("E1809"), refused("""
                module example.local

                data Count = Int

                behavior twice : (a: Int, b: Int) -> Count
                    constructs Count
                let twice (a, b) = {
                    let decide = (p, x) -> if p(x) then 1 else 0
                    Count(decide(n -> n < 18, a) + decide(m -> 65 <= m, b))
                }
                """));
    }

    /** And one handed to a name the body bound a declaration to. */
    @Test
    void aDeclarationBoundByALetTakesNoRuleEither() {
        assertEquals(List.of("E1809"), refused("""
                module example.local

                data Yes
                data No
                data Verdict = Yes | No
                data Count = Int

                let choose (p: (Int) -> Bool, x: Int): Verdict =
                    if p(x) then Yes else No

                behavior twice : (a: Int, b: Int) -> Count
                    constructs Count
                let twice (a, b) = {
                    let f = choose
                    Count((if f(n -> n < 18, a) == Yes then 1 else 0)
                        + (if f(m -> 18 <= m, b) == Yes then 1 else 0))
                }
                """));
    }

    /** What a name bound to a block does take is a value, and a fork inside it is its own. */
    @Test
    void aBlockBoundByALetTakesValues() {
        assertEquals(List.of(), refused("""
                module example.local

                data Count = Int

                behavior once : (a: Int) -> Count
                    constructs Count
                let once (a) = {
                    let decide = (x) -> if x < 18 then 1 else 0
                    Count(decide(a))
                }
                """));
    }
}
