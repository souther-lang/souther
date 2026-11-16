package souther.compiler.partition;

import souther.compiler.ACompiledModel;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.Map;

/** Ways of holding a row for the tests of what is said of several of them together. */
final class HeldOutcomeFixtures {

    private static final SearchRegion REGION = region();

    private HeldOutcomeFixtures() { }

    /** One way of holding a row, to a truth of {@code position}, over nothing on the way. Two
     *  of these are the same way where they are of one position. */
    static HeldOutcome aWayAt(String position) {
        return new HeldOutcome(List.of(new RowDemand.ATruth(TermPath.of(position), true)),
                List.of(), WayToTheBorder.UNTOUCHED, Map.of(), Reachability.untouched(REGION));
    }

    private static SearchRegion region() {
        Compilation compilation = ACompiledModel.answered("""
                module m

                behavior f : (open: Bool) -> Int
                let f (open) = if open then 1 else 0
                """);
        String module = compilation.modules().get(0);
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        Map<String, InputDomain> inputs =
                compilation.db().ask(new Adequacy.Inputs(module)).value();
        return inputs.get("f").reading(rules).quantities().region();
    }
}
