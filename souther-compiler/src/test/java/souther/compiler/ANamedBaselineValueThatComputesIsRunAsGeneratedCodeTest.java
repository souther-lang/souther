package souther.compiler;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;

/**
 * A row may name a module-level value whose own body computes, not only one that stands for a
 * literal or a plain construction. The value is never published — nothing but the row reaches it by
 * name — so a fixture entry is minted for it rather than reused from one the module already carries
 * for another module to call.
 */
class ANamedBaselineValueThatComputesIsRunAsGeneratedCodeTest {

    @Test
    void aPrivateBaselineWithAComputedFieldIsNamedByARow() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo

                data Amount = Decimal
                data Order = { total: Amount }
                data Accepted
                data Rejected

                let baseline = Order { total = Amount(1.5m + 2.5m) }

                behavior settle : (o: Order) -> Accepted | Rejected

                let settle (o) = if o.total == Amount(4.0m) then Accepted else Rejected

                example settle
                    | "a baseline whose total was computed" : (baseline) -> Accepted
                """));
    }

    @Test
    void anAttachedFilesBaselineWithAComputedFieldIsNamedByARow() {
        assertDoesNotThrow(() -> Compiler.compileModules(List.of("""
                module demo

                data Amount = Decimal
                data Order = { total: Amount }
                data Accepted
                data Rejected

                behavior settle : (o: Order) -> Accepted | Rejected

                let settle (o) = if o.total == Amount(4.0m) then Accepted else Rejected
                """, """
                examples for demo

                let baseline = Order { total = Amount(1.5m + 2.5m) }

                example settle
                    | "an attached baseline whose total was computed" : (baseline) -> Accepted
                """)));
    }
}
