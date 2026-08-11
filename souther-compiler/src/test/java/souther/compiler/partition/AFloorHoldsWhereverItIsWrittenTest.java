package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Ast;
import souther.compiler.check.FieldDomains;
import souther.compiler.check.Symbols;
import souther.compiler.query.Compilation;
import souther.compiler.query.Shapes;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * How much a position has to hold, where two things can say so.
 *
 * <p>A rule counting a value is written either on that value's own type or on the record that has it
 * as a field, and both are rules the construction has to satisfy. Read one of them and a position is
 * offered a value the other refuses — which is #650, where a field's list was offered the empty one
 * because the floor was the record's and only the type's was read.
 */
class AFloorHoldsWhereverItIsWrittenTest {

    private record Model(Symbols symbols, String module) {

        FieldDomains domainsOf(String type) {
            TypeName named = new TypeName(module, type);
            Ast.Data data = (Ast.Data) symbols.get(named);
            assertNotNull(data, "no `" + type + "`");
            return FieldDomains.of(named, data, symbols);
        }

        Type ref(String type) {
            return new Type.Ref(new TypeName(module, type));
        }
    }

    private static Model modelOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Symbols symbols = compilation.db().ask(new Shapes.Scope(module)).value();
        assertNotNull(symbols, "the model did not compile");
        return new Model(symbols, module);
    }

    /** The record's rule, at a field whose own type says nothing. */
    @Test
    void aRecordsRuleIsAFloorAtTheFieldItCounts() {
        Model model = modelOf("""
                module example.bag

                data Bag =
                    { xs: List<Int>
                    }
                    invariant atLeastTwo = List.length(xs) >= 2
                """);

        assertEquals(2, Partitions.leastHeld(new Type.ListOf(Type.INT), model.symbols(),
                model.domainsOf("Bag").heldAt("xs")));
    }

    /** And the type's own rule where the record says nothing, which is the reading that already
     * worked and has to keep working. */
    @Test
    void aTypesOwnRuleIsStillAFloorWhereNoRecordSpeaks() {
        Model model = modelOf("""
                module example.bag

                data NonEmpty = List<Int>
                    invariant atLeastOne = List.length(value) >= 1

                data Bag = { xs: NonEmpty }
                """);

        assertEquals(1, Partitions.leastHeld(model.ref("NonEmpty"), model.symbols(),
                model.domainsOf("Bag").heldAt("xs")));
    }

    /**
     * And the higher of the two where both speak.
     *
     * <p>Both are rules the construction has to satisfy, so a value clearing one and not the other is
     * refused as surely as one clearing neither. Taking the record's alone would offer a list of two
     * where the type asks for three; taking the type's alone is #650 again.
     */
    @Test
    void theHigherOfTheTwoIsWhatHasToHold() {
        Model model = modelOf("""
                module example.bag

                data AtLeastThree = List<Int>
                    invariant atLeastThree = List.length(value) >= 3

                data Bag =
                    { xs: AtLeastThree
                    }
                    invariant atLeastTwo = List.length(xs.value) >= 2
                """);

        assertEquals(3, Partitions.leastHeld(model.ref("AtLeastThree"), model.symbols(),
                model.domainsOf("Bag").heldAt("xs")));
    }

    /**
     * A rule bounding only a sum of two counts is a floor under neither of them.
     *
     * <p>Either list may hold nothing as long as the other does not, so the value that holds nothing
     * is one the rule admits at both positions. Held because a reading that finds a floor here is one
     * that would put a floor under every field a rule so much as names.
     */
    @Test
    void aRuleOverASumOfTwoCountsIsAFloorUnderNeither() {
        Model model = modelOf("""
                module example.duplicate

                data Possible =
                    { accounts: List<Int>
                    , contacts: List<Int>
                    }
                    invariant oneOfThem = List.length(accounts) + List.length(contacts) >= 1
                """);
        FieldDomains domains = model.domainsOf("Possible");

        assertEquals(0, Partitions.leastHeld(new Type.ListOf(Type.INT), model.symbols(),
                domains.heldAt("accounts")), "an empty list of accounts stands beside a contact");
        assertEquals(0, Partitions.leastHeld(new Type.ListOf(Type.INT), model.symbols(),
                domains.heldAt("contacts")), "and the same the other way round");
    }
}
