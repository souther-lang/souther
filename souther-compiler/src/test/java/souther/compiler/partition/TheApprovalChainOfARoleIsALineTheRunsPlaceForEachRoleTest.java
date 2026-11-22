package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import souther.compiler.ACompiledModel;
import souther.compiler.NotRead;
import souther.compiler.ast.Hir;
import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.meaning.CasesHeldTo;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.OfferingRequest;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.WhyAPlaceIsUndividedIsSaid;
import souther.compiler.types.TypeSymbol;
import souther.test.Nightly;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comparison of how long the answer of a called behavior is draws its caller a line the runs
 * place, once for each case the other side is chosen by, and rows stand on it by what their runs
 * worked out. Apart from the other readings of a searched line because composing the rows and
 * running the model again costs more than a change waits for.
 */
@Nightly
class TheApprovalChainOfARoleIsALineTheRunsPlaceForEachRoleTest {

    /**
     * The line to the submitter is searched for in the body of a behavior the approval chain
     * calls, and that search is the called behavior's own account. To the caller the length of
     * what the call answered is a number a run works out: its comparison with how many the role
     * needs is a line the runs place, drawn once for each role, and a row stands at a point of
     * it by what its run worked out.
     */
    @Test
    void theApprovalChainOfARoleIsALineTheRunsPlaceForEachRole() {
        String model = """
                module demo

                data UserId = String
                    invariant String.length(value) >= 1
                data RoleName = String
                    invariant String.length(value) >= 1
                data RoleNode =
                    { role: RoleName
                    , holder: UserId
                    , reports: List<RoleNode>
                    }
                data ReportingChain = { steps: List<UserId> }
                data NotInHierarchy = { user: UserId }

                let pathTo (node: RoleNode, user: UserId): List<UserId> =
                    if node.holder == user
                        then [ node.holder ]
                        else {
                            let below = List.fold((found, r) ->
                                    if List.isEmpty(found) then pathTo(r, user) else found,
                                [], node.reports)
                            if List.isEmpty(below) then [] else [ node.holder ] ++ below
                        }

                behavior chainTo : (root: RoleNode, user: UserId) -> ReportingChain | NotInHierarchy
                    constructs ReportingChain, NotInHierarchy
                let chainTo (root, user) = {
                    let steps = pathTo(root, user)
                    guard Bool.not(List.isEmpty(steps)) else NotInHierarchy { user = user }
                    ReportingChain { steps = steps }
                }

                data SalesManager
                data RegionalVp
                data Cfo
                data ApproverRole = SalesManager | RegionalVp | Cfo
                data ApprovalChain = { role: ApproverRole, approvers: List<UserId> }
                data SubmitterNotInHierarchy = { submitter: UserId }
                data NoAuthorityAbove = { submitter: UserId, needed: Int, available: Int }

                let levelsFor (role: ApproverRole): Int =
                    match role with
                        | SalesManager -> 1
                        | RegionalVp   -> 2
                        | Cfo          -> 3

                behavior approvalChainFor : (root: RoleNode, submitter: UserId, role: ApproverRole)
                        -> ApprovalChain | SubmitterNotInHierarchy | NoAuthorityAbove
                    constructs ApprovalChain, SubmitterNotInHierarchy, NoAuthorityAbove

                let approvalChainFor (root, submitter, role) =
                    match chainTo(root, submitter) with
                        | NotInHierarchy -> SubmitterNotInHierarchy { submitter = submitter }
                        | ReportingChain as line -> {
                            let above = List.drop(1, List.reverse(line.steps))
                            let needed = levelsFor(role)
                            guard List.length(above) >= needed
                                else NoAuthorityAbove { submitter = submitter, needed = needed
                                                      , available = List.length(above) }
                            ApprovalChain { role = role, approvers = List.take(needed, above) }
                        }

                let acmeOrg = RoleNode { role = RoleName("CEO"), holder = UserId("u-ceo"), reports =
                    [ RoleNode { role = RoleName("VP"), holder = UserId("u-vp"), reports =
                        [ RoleNode { role = RoleName("Mgr"), holder = UserId("u-mgr"), reports =
                            [ RoleNode { role = RoleName("Rep"), holder = UserId("u-rep"), reports = [] } ] } ] } ] }

                example approvalChainFor
                    | "one above" : (acmeOrg, UserId("u-mgr"), SalesManager)
                        -> ApprovalChain { role = SalesManager, approvers = [ UserId("u-vp") ] }
                    | "ghost" : (acmeOrg, UserId("u-ghost"), SalesManager)
                        -> SubmitterNotInHierarchy { submitter = UserId("u-ghost") }
                    | "ceo" : (acmeOrg, UserId("u-ceo"), SalesManager)
                        -> NoAuthorityAbove { submitter = UserId("u-ceo"), needed = 1, available = 0 }
                """;
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        ACompiledModel.compiles(compilation);
        AdequacyReport report = AdequacyReport.of(compilation);
        String json = report.json(SourceRendering.namedByIdentity(SourceLayouts.NONE));
        String human = report.humanInEnglish(SourceRendering.namedByIdentity(SourceLayouts.NONE));
        assertFalse(json.contains("rule_about_a_derived_value"), human);
        assertFalse(json.contains("searched_line"), human);
        assertTrue(json.contains("compared_on_a_run"), human);
        String ofTheChain = human.substring(human.indexOf("  approvalChainFor "));
        assertFalse(NotRead.in(ofTheChain), human);
        assertTrue(ofTheChain.contains(WhyAPlaceIsUndividedIsSaid.of(
                UndividedPosition.Reason.RULE_MEASURED_ON_ITS_RUNS)), human);
        assertTrue(ofTheChain.contains("borders 3"), human);
        for (String role : List.of("SalesManager", "RegionalVp", "Cfo")) {
            assertTrue(ofTheChain.contains("where role is " + role), human);
        }
        // The rows offered are composed without the search, which is the called behavior's: written
        // back as examples they are run by the language, and what they reach is read.
        List<List<FixtureTemplate>> offeredRows = Adequacy.offeredFor(compilation.db(),
                        OfferingRequest.overTheModule("demo"))
                .rowsByBehavior().getOrDefault("approvalChainFor", List.of()).stream()
                .map(row -> row.inputs()).toList();
        // Beside them, rows over the tree of the model toward the points of each role's line.
        StringBuilder written = new StringBuilder("""
                | "vp, one" : (acmeOrg, UserId("u-vp"), SalesManager)
                    -> ApprovalChain { role = SalesManager, approvers = [ UserId("u-ceo") ] }
                | "rep, two" : (acmeOrg, UserId("u-rep"), RegionalVp)
                    -> ApprovalChain { role = RegionalVp
                                     , approvers = [ UserId("u-mgr"), UserId("u-vp") ] }
                | "mgr, two" : (acmeOrg, UserId("u-mgr"), RegionalVp)
                    -> ApprovalChain { role = RegionalVp
                                     , approvers = [ UserId("u-vp"), UserId("u-ceo") ] }
                | "vp, two" : (acmeOrg, UserId("u-vp"), RegionalVp)
                    -> NoAuthorityAbove { submitter = UserId("u-vp"), needed = 2, available = 1 }
                | "rep, three" : (acmeOrg, UserId("u-rep"), Cfo)
                    -> ApprovalChain { role = Cfo, approvers =
                        [ UserId("u-mgr"), UserId("u-vp"), UserId("u-ceo") ] }
                | "mgr, three" : (acmeOrg, UserId("u-mgr"), Cfo)
                    -> NoAuthorityAbove { submitter = UserId("u-mgr"), needed = 3, available = 2 }
            """);
        int named = 0;
        for (List<FixtureTemplate> row : offeredRows) {
            List<String> inputs = row.stream().map(FixtureTemplate::text).toList();
            String role = inputs.get(2);
            int needed = switch (role) {
                case "SalesManager" -> 1;
                case "RegionalVp" -> 2;
                case "Cfo" -> 3;
                default -> throw new AssertionError("a role this model does not have: " + role);
            };
            Optional<List<String>> above = holdersAbove(row.get(0).value(), row.get(1).value());
            String answer;
            if (above.isEmpty()) {
                answer = "SubmitterNotInHierarchy { submitter = " + inputs.get(1) + " }";
            } else if (above.get().size() >= needed) {
                answer = "ApprovalChain { role = " + role + ", approvers = [ "
                        + above.get().subList(0, needed).stream()
                                .map(holder -> "UserId(" + FixtureTemplate.string(holder).text() + ")")
                                .collect(Collectors.joining(", "))
                        + " ] }";
            } else {
                answer = "NoAuthorityAbove { submitter = " + inputs.get(1) + ", needed = " + needed
                        + ", available = " + above.get().size() + " }";
            }
            written.append("                | \"offered ").append(named++).append("\" : (")
                    .append(String.join(", ", inputs)).append(") -> ").append(answer)
                    .append('\n');
        }
        Compilation after = measuredModel(model + written);
        List<BorderAssessment.Point> owed = BorderAssessment.pointsOf(
                        Adequacy.boundariesOf(after.db(), "demo").get("approvalChainFor"))
                .stream().filter(point -> point.owed() != null)
                .filter(point -> roleOfALine(point) != null)
                .toList();
        // Each line is at how many stand above the submitter less how many the role needs, and a
        // row stands where its run worked that out: at the ON and OFF point of every role's line
        // and past the line of the roles the tree has room for, by the rows over the tree; short
        // of the line by more than one, by the rows offered, whose tree is the submitter alone.
        // More points may come to be met, so these are a floor.
        Set<LinePoint> met = owed.stream().filter(point -> point.owed().hasRowWitness())
                .map(TheApprovalChainOfARoleIsALineTheRunsPlaceForEachRoleTest::linePointOf)
                .filter(Objects::nonNull).collect(Collectors.toSet());
        assertTrue(met.containsAll(Set.of(
                        new LinePoint(PointRole.IN, "SalesManager", ExactRatio.of(0)),
                        new LinePoint(PointRole.IN, "RegionalVp", ExactRatio.of(0)),
                        new LinePoint(PointRole.ON, "SalesManager", ExactRatio.of(0)),
                        new LinePoint(PointRole.ON, "RegionalVp", ExactRatio.of(0)),
                        new LinePoint(PointRole.ON, "Cfo", ExactRatio.of(0)),
                        new LinePoint(PointRole.OFF, "SalesManager", ExactRatio.of(-1)),
                        new LinePoint(PointRole.OFF, "RegionalVp", ExactRatio.of(-1)),
                        new LinePoint(PointRole.OFF, "Cfo", ExactRatio.of(-1)),
                        new LinePoint(PointRole.OUT, "RegionalVp", ExactRatio.of(-1)),
                        new LinePoint(PointRole.OUT, "Cfo", ExactRatio.of(-1)))),
                () -> "met " + met);
        // What is left owed is past the line of the role the tree has no room for, and short by
        // more than one of the line of the role that needs one, where fewer than none would stand
        // above the submitter.
        Set<LinePoint> unmet = owed.stream().filter(point -> !point.owed().hasRowWitness())
                .map(TheApprovalChainOfARoleIsALineTheRunsPlaceForEachRoleTest::linePointOf)
                .filter(Objects::nonNull).collect(Collectors.toSet());
        assertTrue(Set.of(new LinePoint(PointRole.IN, "Cfo", ExactRatio.of(0)),
                        new LinePoint(PointRole.OUT, "SalesManager", ExactRatio.of(-1)))
                .containsAll(unmet), () -> "left owed " + unmet);
    }

    private static Compilation measuredModel(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        return ACompiledModel.compiles(compilation);
    }

    /** A point of a line a comparison of the line's length draws, by what makes it that one. */
    private record LinePoint(PointRole role, String roleCase, ExactRatio at) {}

    /** The point by its role, the role of the input its line is decided in and the number it is
     *  anchored at; null where it is anchored at no number a row can be written at. */
    private static LinePoint linePointOf(BorderAssessment.Point point) {
        ExactRatio at = point.owed().criterion().anchor().asANumber();
        return at == null ? null
                : new LinePoint(point.role(), roleOfALine(point), at);
    }

    /**
     * The name of the one role the line of {@code point} is decided in, or null for a line that
     * is decided in no case of the input.
     */
    private static String roleOfALine(BorderAssessment.Point point) {
        if (!(point.border().border().origin() instanceof LineOrigin.ComparisonOrigin origin)
                || origin.part().isEmpty()) {
            return null;
        }
        Set<String> named = new LinkedHashSet<>();
        CasesHeldTo.of(origin.part().get().decides()).forEach((at, held) -> {
            if (held instanceof CasesHeldTo.Held.OneOf(var cases)) {
                cases.leavesOfASum().forEach(leaf ->
                        named.add(assertInstanceOf(TypeSymbol.AtModule.class, leaf).name()));
            }
        });
        return named.size() == 1 ? named.iterator().next() : null;
    }

    /**
     * The holders of the nodes above the first node, met in the order a search reads the tree,
     * that holds {@code submitter}, the nearest first; nothing where no node holds it.
     */
    private static Optional<List<String>> holdersAbove(Hir.Expr tree, Hir.Expr submitter) {
        return pathTo(tree, textOf(submitter)).map(path ->
                path.subList(0, path.size() - 1).reversed());
    }

    /** The holders from {@code node} down to the first node, before its siblings, that holds {@code
     *  holder}. */
    private static Optional<List<String>> pathTo(Hir.Expr node, String holder) {
        Map<String, Hir.Expr> fields = new LinkedHashMap<>();
        Hir.NewData data = assertInstanceOf(Hir.NewData.class, node);
        data.inits().forEach(init -> fields.put(String.valueOf(init.written()), init.value()));
        String here = textOf(fields.get("holder"));
        if (here.equals(holder)) {
            return Optional.of(List.of(here));
        }
        for (Hir.Expr below : assertInstanceOf(Hir.ListLit.class, fields.get("reports"))
                .elements()) {
            Optional<List<String>> found = pathTo(below, holder);
            if (found.isPresent()) {
                List<String> path = new ArrayList<>();
                path.add(here);
                path.addAll(found.get());
                return Optional.of(path);
            }
        }
        return Optional.empty();
    }

    /** The string a newtype of one is applied to. */
    private static String textOf(Hir.Expr newtype) {
        Hir.Apply apply = assertInstanceOf(Hir.Apply.class, newtype);
        return assertInstanceOf(Hir.StringLit.class, apply.args().getFirst()).value();
    }
}
