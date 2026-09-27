package souther.architecture;

import org.junit.jupiter.api.Test;

/**
 * Scratch dump for #2011 triage. Not a permanent check — prints every refusable
 * {@code BigDecimal} call {@code souther-compiler} makes, one per line, for the triage that decides
 * {@link souther.architecture.WhoMayAskCompilerCallSitesWhatTheyCanRefuseTest} (not written yet).
 * Deleted once that test exists.
 */
class DumpCompilerBigDecimalCallsTest {

    @Test
    void dump() {
        CompiledOutputs compiled = CompiledOutputs.ofWhatThisRepositoryPublishes();
        BigDecimalCalls.in(compiled.classesOf(compiled.module("souther-compiler"))).stream()
                .map(BigDecimalCalls.Call::row)
                .sorted()
                .forEach(System.out::println);
    }
}
