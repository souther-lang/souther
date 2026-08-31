package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.check.FieldDomains;
import souther.compiler.check.Owed;
import souther.compiler.check.Prepared;
import souther.compiler.check.RuleKey;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.query.Scopes;
import souther.compiler.query.Shapes;
import souther.compiler.types.TypeSymbol;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * Where a rule wrote a name is one question, and it is asked once.
 *
 * <p>A rule reaches a location in four spellings — the term an axis is measured at, the term a
 * comparison drew, the coordinate a clause placed an end on, the position a clause admits values at
 * — and what differs between them is what the rule says, never where it says it. So the address
 * comes out the same from all four, and what is left over keeps each of them apart.
 */
class ANameIsReadOnceHoweverTheRuleSpelledItTest {

    /** Two records of one field, one of which is bounded on a number taken of that field. */
    private static final String TWO_WAYS = """
            module g

            data Measured = { name: String }
                invariant long = String.length(name) >= 3
            data Plain = { name: String }

            data Ok

            behavior byLength : (h: Measured) -> Ok
            behavior byValue : (h: Plain) -> Ok
            """;

    private static final String SHARED = """
            module g

            data Paging = { limit: Int }
            data A = { ...Paging, x: Int }
            data B = { ...Paging, y: Int }
            data Q = A | B

            data Ok

            behavior read : (q: Q) -> Ok
            """;

    /**
     * The number a rule is about does not move where it was written.
     *
     * <p>{@code String.length(h.name)} and {@code h.name} are two numbers of one location. A reader
     * that took the address off the number would have two names for that location, and a rule about
     * one of them would be filed where the other was.
     */
    @Test
    void aNumberTakenOfALocationIsWrittenWhereTheLocationIs() {
        NumericTerm taken = termAt(TWO_WAYS, "byLength", "h", "name");
        NumericTerm own = termAt(TWO_WAYS, "byValue", "h", "name");
        assertInstanceOf(NumericTerm.TakenOf.class, taken, "this one is bounded on its length");
        assertInstanceOf(NumericTerm.ValueOf.class, own, "and this one on its own values");

        TermPath root = TermPath.of("h");
        souther.compiler.check.RuleRef.Invariant rule = someRule(measuredIn(TWO_WAYS));
        assertEquals(PlacementSeed.of(root, own, rule, someCitation(rule)).address(),
                PlacementSeed.of(root, taken, rule, someCitation(rule)).address());
        assertNotEquals(PlacementSeed.of(root, own, rule, someCitation(rule)).placed(),
                PlacementSeed.of(root, taken, rule, someCitation(rule)).placed(),
                "and what each says about the location is what tells them apart");
    }

    /**
     * A question about the values at a location and a line on a number of it are written at the one
     * address.
     *
     * <p>Two questions and one place. What is left of each once the address is out of it is what a
     * reader has to keep apart, and it is the whole of what a reader has to keep apart.
     */
    @Test
    void twoQuestionsAboutOneLocationAreAtOneAddress() {
        TermPath root = TermPath.of("h");
        souther.compiler.check.RuleRef.Invariant rule = someRule(measuredIn(TWO_WAYS));
        PlacementSeed values = PlacementSeed.of(root,
                new Owed.AdmittedValues(RuleKey.of("name")), rule, someCitation(rule));
        PlacementSeed line = PlacementSeed.of(root,
                new Owed.Boundary(FieldDomains.Coordinate.value(RuleKey.of("name"))), rule,
                someCitation(rule));

        assertEquals(values.address(), line.address());
        assertEquals(new PlacementSeed.Placed.TheValuesThere(), values.placed());
        assertEquals(new PlacementSeed.Placed.ANumberOfIt(
                        new FieldDomains.CoordinateKind.OfItsOwnValue()), line.placed());
    }

    /**
     * One name under two values is two names.
     *
     * <p>A clause is not written across a narrowing, so what a {@code Q} calls {@code limit} and
     * what an {@code A} calls {@code limit} are written in different declarations. Held as the name
     * alone, a rule of one case would answer for the same field of every other.
     */
    @Test
    void oneKeyUnderTwoValuesIsTwoAddresses() {
        InputDomain read = reading(SHARED, "read");
        TermPath sum = TermPath.of("q");
        TermPath aCase = sum.refine(Refinement.sumCase(caseNamed(read, sum, "A")));

        assertNotEquals(new RuleAddress(sum, RuleKey.of("limit")),
                new RuleAddress(aCase, RuleKey.of("limit")));
    }

    /**
     * A path no rule of the value can name places nothing, and is not a placement that reached
     * nowhere.
     *
     * <p>The reading of one value has nothing to say about a position in another, and that is what
     * this answers. Turned into a placement here, every clause that keeps to its own value would be
     * a rule somebody failed to file.
     */
    @Test
    void aPathUnderAnotherValuePlacesNothing() {
        InputDomain read = reading(SHARED, "read");
        TermPath sum = TermPath.of("q");
        TermPath a = sum.refine(Refinement.sumCase(caseNamed(read, sum, "A")));
        TermPath b = sum.refine(Refinement.sumCase(caseNamed(read, sum, "B")));

        assertNull(RuleAddress.of(a, b.then("limit")),
                "no rule of `A` names a position in `B`");
        assertNull(RuleAddress.of(sum, a.then("limit")),
                "and the sum's own rules do not reach into a case either: what relates a name at "
                        + "the sum to that position is the crossing, and an address that stepped "
                        + "through the narrowing would be a second way to say it");
        souther.compiler.check.RuleRef.Invariant rule = someRule(caseNamedAtModule(read, sum, "A"));
        assertNull(PlacementSeed.of(a, new NumericTerm.ValueOf(b.then("limit")), rule,
                        someCitation(rule)),
                "so nothing was placed there, which is not the same as a placement with nowhere "
                        + "to go");
        assertNotNull(PlacementSeed.of(a, new NumericTerm.ValueOf(a.then("limit")), rule,
                        someCitation(rule)),
                "and the same rule about its own value does place something");
    }

    /** The term the reading measures one position at. */
    private static NumericTerm termAt(String source, String behavior, String parameter,
                                      String field) {
        Position at = reading(source, behavior).at(TermPath.of(parameter).then(field));
        assertNotNull(at, "the field is a position of the input");
        return at.term();
    }

    /** The case's own name, taken off the reading that holds it. */
    private static TypeSymbol caseNamed(InputDomain read, TermPath sum, String name) {
        for (Case each : read.at(sum).obligationCases()) {
            if (each instanceof Case.SumCase one && one.leaf().name().equals(name)) {
                return one.leaf();
            }
        }
        throw new IllegalStateException("no case named " + name);
    }

    /** A declaration of the model to hang a made-up rule on. */
    private static TypeSymbol.AtModule measuredIn(String source) {
        souther.compiler.types.Type type =
                reading(source, "byLength").at(TermPath.of("h")).view().declared();
        if (type instanceof souther.compiler.types.Type.Ref ref
                && ref.name() instanceof TypeSymbol.AtModule at) {
            return at;
        }
        throw new IllegalStateException("the parameter is a declaration of the module");
    }

    /** The case's own name, where a declaration is what is wanted. */
    private static TypeSymbol.AtModule caseNamedAtModule(InputDomain read, TermPath sum,
                                                         String name) {
        return (TypeSymbol.AtModule) caseNamed(read, sum, name);
    }

    /** A rule to hang a placement on, so that a seed made here is one some rule placed. */
    private static souther.compiler.check.RuleRef.Invariant someRule(
            souther.compiler.types.TypeSymbol.AtModule on) {
        return new souther.compiler.check.RuleRef.Invariant(
                new souther.compiler.check.Clause.Ref(
                        new souther.compiler.check.Clause.Id(on, 0),
                        java.util.Optional.of(new souther.compiler.check.ClauseName("here"))));
    }

    /** How a report would send a reader to it. */
    private static souther.compiler.check.RuleCitation someCitation(
            souther.compiler.check.RuleRef.Invariant rule) {
        return souther.compiler.check.RuleCitation.named(rule);
    }

    private static InputDomain reading(String source, String behavior) {
        Compilation compilation =
                Compilation.ofSources(List.of(source), souther.compiler.meta.ModulePath.EMPTY);
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Prepared prepared = compilation.db().ask(new Shapes.Prepared(module)).value();
        Map<String, Sig> sigs = compilation.db().ask(new Bodies.Signatures(module)).value();
        Symbols symbols = Scopes.derived(compilation.db(), module).value();
        Hir.SpecBehavior spec = (Hir.SpecBehavior) prepared.behaviors().stream()
                .filter(b -> b.name().equals(behavior)).findFirst().orElseThrow();
        return InputDomain.of(spec, sigs.get(behavior), symbols, ReadAs.THE_COMPILATION_DOES);
    }
}
