package souther.compiler.check;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.lang.classfile.ClassFile;
import java.lang.classfile.ClassModel;
import java.lang.classfile.FieldModel;
import java.lang.classfile.MethodModel;
import java.lang.classfile.instruction.InvokeInstruction;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * Everything that still carries an operator, and what each of them wants it for.
 *
 * <p>Beside {@link AnOperatorIsAskedWhatItPlacesInOnePlaceTest}, which says how often an operator
 * may be read for what it places. That one holds the crossings between how a comparison is written
 * and what it means to one call each; this one is the list of everywhere an operator can still
 * reach, so that somewhere new is a line that has to be written down and given a reason.
 *
 * <p><b>A list and not a count.</b> A number stays right while one hold goes and another arrives,
 * and the arriving one is exactly what this is for.
 *
 * <p>Read off the compiled classes, so what a method or a field carries is what the class file
 * says. Which of them read the operator for what it <em>means</em> is not something a descriptor
 * shows, and the reasons below are where that is said.
 */
class WhereAnOperatorMayStillBeHeldIsWrittenDownTest {

    private static final String BIN_OP = "Lsouther/compiler/types/BinOp;";

    private static final String OPERATOR = "souther/compiler/types/BinOp";

    private static final String COMPARISON = "souther/compiler/check/Comparison";

    private static final String BINARY = "souther/compiler/core/Core$Binary";

    private static final String HIR_BINARY = "souther/compiler/ast/Hir$Binary";

    /** A method or a field that carries an operator, and what it carries one for. */
    private record Held(String what, String why) { }

    private static final List<Held> MAY_HOLD = List.of(
            new Held("souther.compiler.ast.Hir.Binary#op",
                    "the resolved tree, which is where an operator is written down"),
            new Held("souther.compiler.ast.Hir.Binary.op", "the same, read"),
            new Held("souther.compiler.core.Core.Binary#op",
                    "the tree a check produces, which carries what the source wrote"),
            new Held("souther.compiler.core.Core.Binary.op", "the same, read"),

            new Held("souther.compiler.check.ComparisonPlacement.of",
                    "the one reading of an operator for what it places"),
            new Held("souther.compiler.check.ComparisonWriting.operatorStating",
                    "the one writing of a relation as an operator, for a comparison composed out"
                            + " of what the rules proved"),

            new Held("souther.compiler.check.ArithmeticCheck.of",
                    "which operands an operator takes and what it answers, which is a question"
                            + " about the operator itself"),
            new Held("souther.compiler.check.BinaryElaborator.operandBeside",
                    "the type the other operand has to have, likewise"),
            new Held("souther.compiler.check.HelperParams.BodyTyping.visitOperand",
                    "types an operand under the operator it stands beside"),
            new Held("souther.compiler.check.ConstEval.arith",
                    "what the operator computes of two constants"),
            new Held("souther.compiler.check.ConstEval.compare", "the same for a comparison"),
            new Held("souther.compiler.codegen.BodyGen.comparisonMaterialize",
                    "which instructions an operator is emitted as"),
            new Held("souther.compiler.check.Terms.isArith",
                    "which operators compute a number, spelled as four equalities rather than"
                            + " asked of the operator: a membership the enum does not own, and one"
                            + " an operator added later falls quietly outside of"),
            new Held("souther.compiler.partition.Condition.combines",
                    "which operators put conditions together, spelled as two equalities — the same"
                            + " set the enum already answers for, under another name"),

            new Held("souther.compiler.check.Conditions.comparison",
                    "builds a node from the operator it is handed"),
            new Held("souther.compiler.reading.Meetings.run",
                    "walks the operands under the operator they are written with"),

            new Held("souther.compiler.check.DischargeRules.operator",
                    "which operator a library operation is defined as"),
            new Held("souther.compiler.semantics.Arithmetic.TheOperator#op",
                    "a library operation declared to compute what an operator computes"),
            new Held("souther.compiler.semantics.Arithmetic.TheOperator.op", "the same, read"),
            new Held("souther.compiler.semantics.NumericResult.TheOtherCaseWhen#op",
                    "a library fact stating the case an operation answers something else in, as a"
                            + " comparison against a number: an operator standing for what it"
                            + " means, in a table nothing recognises a comparison out of"),
            new Held("souther.compiler.semantics.NumericResult.TheOtherCaseWhen.op",
                    "the same, read"),

            new Held("souther.compiler.check.NumericMeaning.Operator#op",
                    "an arithmetic expression keyed by the operator written in it"),
            new Held("souther.compiler.check.NumericMeaning.Operator.op", "the same, read"),
            new Held("souther.compiler.check.Terms.written",
                    "makes the term a written binary is, off the operator it was written with"),
            new Held("souther.compiler.check.Term.Interner.operator",
                    "which of the canonical terms a comparison is: the same six-into-three the"
                            + " reading of a guard now takes from what was placed, kept here in the"
                            + " operator's own words"),
            new Held("souther.compiler.coverage.SourceOutcome.Compared#op",
                    "the operator an outcome was written with, which is what a report shows"),
            new Held("souther.compiler.coverage.SourceOutcome.Compared.op", "the same, read"));

    /** The one walk that has both, and what each of them is. */
    private static final Held WALKS_TO_A_COMPARISON = new Held(
            "souther.compiler.partition.EnsuresThresholds.stated",
            "the walk down a clause reaches a comparison partway. The operators it reads are a"
                    + " conjunction's and a disjunction's, both on statements it has not recognised"
                    + " as comparisons and neither of which it goes on to read — a conjunction is"
                    + " walked into and what a disjunction states is neither of its sides. The node"
                    + " it takes from the comparison it did recognise is where a finding is filed,"
                    + " and nothing asks it for an operator.");

    /**
     * Everything that reaches into a tree for an operator and decides on what it finds.
     *
     * <p>What the descriptor list beside this cannot see. A reading that takes the operator out of
     * a node and switches on it there and then puts one in no signature and holds one in no field,
     * so a new table written that way arrives in nothing that is declared — which is the shape this
     * whole change is about, and the one it would have been least able to stop.
     *
     * <p><b>Taking is not deciding.</b> A pass that copies a tree reads every operator it meets and
     * writes each one back into the node it is rebuilding, and there is nothing to say about that.
     * What is here is a method that both gets hold of an operator and asks it something: names one
     * of the constants, or switches over them, or puts a question to the enum.
     *
     * <p>Asking the enum its own questions is in the list rather than out of it. {@code compares}
     * and {@code rightRunsWhenLeftIs} are where those memberships live, so a reader consulting them
     * is doing the right thing — and a reader that stops consulting them and spells the set out
     * again is a line here that changes rather than one that appears.
     */
    @Test
    void everyOperatorTakenOutOfATreeIsWrittenDown() {
        assertEquals(declared(TAKEN_FROM_A_TREE), declaredFrom(takesAnOperator()),
                "a reading that takes an operator out of a node and decides on it is a line here"
                        + " with what it decides. What each of these decides: "
                        + why(TAKEN_FROM_A_TREE));
    }

    private static final List<Held> TAKEN_FROM_A_TREE = List.of(
            // Which operators put conditions together, and what each says about its two halves.
            new Held("souther.compiler.check.ClauseExpr.of",
                    "a conjunction asserted true and a disjunction asserted false each state both"
                            + " halves"),
            new Held("souther.compiler.check.ClauseHelpers.conjunctsOf",
                    "the conjuncts of a clause, which is walking into a conjunction"),
            new Held("souther.compiler.check.Conditions.stating",
                    "the same, for what a condition states on its own"),
            new Held("souther.compiler.check.FieldDomains.lambda$projection$2",
                    "walks into a conjunction for the clause that bounds a field"),
            new Held("souther.compiler.check.InvariantChecker.direct",
                    "walks into a conjunction for the clauses an invariant states"),
            new Held("souther.compiler.check.PathReachability.walk",
                    "which way an operator has to come out for the arm under it to be reached"),
            new Held("souther.compiler.check.Predicates.assumeCond",
                    "a conjunction asserted true gives both sides, a disjunction asserted false"
                            + " gives both denied"),
            new Held("souther.compiler.check.Predicates.quantifiedBy",
                    "walks into a conjunction for what it quantifies over"),
            new Held("souther.compiler.check.Predicates.read",
                    "walks into a conjunction for the clauses a rule owes"),
            new Held("souther.compiler.partition.ComparisonReadings.walk",
                    "walks both sides of a conjunction and of a disjunction, each under what the"
                            + " other side leaves"),
            new Held("souther.compiler.partition.Condition.of",
                    "whether the operator joins two conditions, and which of the two it is"),
            new Held("souther.compiler.partition.EnsuresThresholds.stated",
                    "walks into a conjunction, and stops at a disjunction because what one states"
                            + " is neither of its sides"),

            // Which operand runs when, which is the enum's own answer.
            new Held("souther.compiler.core.Evaluated.inOrder",
                    "asks the enum which way the left has to come out for the right to run"),
            new Held("souther.compiler.flow.ValueArrivals.reading",
                    "asks the enum whether the right operand runs on every run"),
            new Held("souther.compiler.flow.ValueArrivals.through", "and which way it runs under"),
            new Held("souther.compiler.reading.CoverageRead.descend",
                    "asks the enum whether the right operand runs on every run"),
            new Held("souther.compiler.reading.CoverageRead.rightOf", "and which way it runs under"),
            new Held("souther.compiler.reading.Meetings.meetingAt",
                    "asks the enum whether the operator stops early, and groups the operands one"
                            + " operator reaches"),

            // What the operator computes, is typed as, or is emitted as.
            new Held("souther.compiler.check.AffineForms.composed",
                    "which arithmetic an expression composes into a form"),
            new Held("souther.compiler.check.BinaryElaborator.elaborateBinary",
                    "what the operator makes of its operands' types"),
            new Held("souther.compiler.check.BinaryElaborator.operand",
                    "the same asked of one operand: a scale takes the base a newtype wraps, and a"
                            + " conjunction takes truths"),
            new Held("souther.compiler.check.ConstEval.binary",
                    "what the operator computes of two constants, and which operand it needs to"
                            + " compute it"),
            new Held("souther.compiler.check.DischargeRules.noSmallerThan",
                    "which operands a string joined by another is no shorter than"),
            new Held("souther.compiler.core.GrowingFold.appended",
                    "what a fold appends, which is what joining strings is"),
            new Held("souther.compiler.examples.FixtureReader.fold",
                    "what the operator computes of two numbers a fixture wrote"),
            new Held("souther.compiler.codegen.BodyGen.binary",
                    "which instructions the operator is emitted as"),
            new Held("souther.compiler.codegen.BodyGen.orderingOf",
                    "which operators are orderings, spelled as four cases rather than asked: a"
                            + " membership the enum does not own, beside the two others spelled"
                            + " outside it"),

            // And the comparisons.
            new Held("souther.compiler.check.InvariantChecker.arithmeticOf",
                    "asks the enum whether the operator compares, which its caller has now"
                            + " recognised the comparison for as well"),
            new Held("souther.compiler.check.Predicates.atomsNamedBy",
                    "asks the enum whether the operator compares: both sides of a comparison are"
                            + " named whatever it states, and anything else is the one value it is"));

    /** Every method that takes an operator out of a tree and decides on what it took. */
    private static List<String> takesAnOperator() {
        List<String> out = new ArrayList<>();
        forEachClass((owner, model) -> {
            for (MethodModel method : model.methods()) {
                boolean takes = false;
                boolean decides = false;
                for (java.lang.classfile.CodeElement element
                        : method.code().map(code -> code.elementList()).orElse(List.of())) {
                    if (element instanceof InvokeInstruction call) {
                        takes |= call.typeSymbol().returnType().descriptorString().equals(BIN_OP)
                                && (call.owner().asInternalName().equals(BINARY)
                                        || call.owner().asInternalName().equals(HIR_BINARY));
                        decides |= call.owner().asInternalName().equals(OPERATOR);
                    }
                    if (element instanceof java.lang.classfile.instruction.FieldInstruction field
                            && field.typeSymbol().descriptorString().equals(BIN_OP)
                            && field.opcode() == java.lang.classfile.Opcode.GETSTATIC) {
                        decides = true;
                    }
                }
                if (takes && decides && !method.methodName().stringValue().startsWith("<")) {
                    out.add(owner + "." + method.methodName().stringValue());
                }
            }
        });
        out.sort(String::compareTo);
        return out;
    }

    @Test
    void everythingCarryingAnOperatorIsWrittenDownWithAReason() {
        assertEquals(declared(MAY_HOLD), carriers(),
                "an operator reaching somewhere new is a line to be written here with what it is"
                        + " wanted for. What each of these carries one for: " + why(MAY_HOLD));
    }

    /**
     * And a comparison's node and an operator are not both to hand, bar one place that says why.
     *
     * <p>A comparison holds its node, because what a body is at is a question about the tree. So
     * the operator is one call away from every reader that has one, and a reader that took it would
     * be answering from the operator below the point where the question was settled — which is what
     * holding the claim exists to stop, and what no count of the crossings would see.
     *
     * <p>Asked of what a method invokes, which is as far as a class file says. Two calls in one
     * body are not proof that the second read what the first handed back; they are proof that
     * whoever wrote it had both to hand, which is what has to be written down.
     */
    @Test
    void aComparisonsNodeAndAnOperatorAreNotBothToHand() {
        assertEquals(List.of(WALKS_TO_A_COMPARISON.what()), bothInOneMethod(),
                WALKS_TO_A_COMPARISON.why());
    }

    /**
     * And who takes the node out of a comparison, which is how the operator stays one call away.
     *
     * <p>Three things are wanted of it and none of them is what the comparison placed: the two
     * sides the rule names, the whole expression to walk, and the place in the tree a reader joins
     * on or files a finding at. The last is why the node is held at all — a body is at a place, and
     * a place is a question about the tree — and it is what keeps the list from being closed by
     * handing out the sides instead.
     *
     * <p>Most of these hand the node on rather than read it, which is what makes the list worth
     * keeping: what travels is the whole node, and every reader it reaches has the operator.
     */
    @Test
    void whoTakesTheNodeOutOfAComparisonIsWrittenDown() {
        assertEquals(declared(TAKES_THE_NODE), declaredFrom(callersOfTheNode()),
                "a reader taking the node has both sides and the operator; what each of these"
                        + " wants it for: " + why(TAKES_THE_NODE));
    }

    /** Everything that asks a comparison for its node, and what for. */
    private static final List<Held> TAKES_THE_NODE = List.of(
            new Held("souther.compiler.coverage.ComparisonCatalog.Catalogued.node",
                    "hands the node back, for a reader joining on the tree"),
            new Held("souther.compiler.coverage.CoverageSites.Plan.requireIsACatalogued",
                    "looks the node up in the catalog, which is keyed by it, and names its place"
                            + " where the two disagree"),
            new Held("souther.compiler.inputs.ComparedNumber.lineOf",
                    "hands the node to the reading that says which of its sides names a position"),
            new Held("souther.compiler.partition.AffineReading.read",
                    "reads the two sides as forms, and hands the node to the reading of which side"
                            + " the rule is about"),
            new Held("souther.compiler.partition.ComparedTerms.asWritten",
                    "reads the two sides for the terms named in them"),
            new Held("souther.compiler.partition.ComparisonAssessment.of",
                    "walks the whole expression for whether the answer is read anywhere in it, and"
                            + " hands it on to the reading of what it cuts"),
            new Held("souther.compiler.partition.ComparisonReadings.Reading.at",
                    "hands the node back, for a reader joining on the tree"),
            new Held("souther.compiler.partition.Condition.Compares.at",
                    "hands the node back as the expression the condition is"),
            new Held("souther.compiler.partition.Cutting.asWritten",
                    "hands the node to the reading of what each place is left with"),
            new Held("souther.compiler.partition.EnsuresThresholds.stated",
                    "files a finding at the node"));

    private static List<String> callersOfTheNode() {
        List<String> out = new ArrayList<>();
        forEachClass((owner, model) -> {
            for (MethodModel method : model.methods()) {
                for (java.lang.classfile.CodeElement element
                        : method.code().map(code -> code.elementList()).orElse(List.of())) {
                    if (element instanceof InvokeInstruction call
                            && call.owner().asInternalName().equals(COMPARISON)
                            && call.name().stringValue().equals("at")) {
                        out.add(owner + "." + method.methodName().stringValue());
                        break;
                    }
                }
            }
        });
        out.sort(String::compareTo);
        return out;
    }

    private static Map<String, String> declared(List<Held> held) {
        Map<String, String> out = new TreeMap<>();
        held.forEach(each -> out.put(each.what(), ""));
        return out;
    }

    private static Map<String, String> why(List<Held> held) {
        Map<String, String> out = new LinkedHashMap<>();
        held.forEach(each -> out.put(each.what(), each.why()));
        return out;
    }

    /** A list of identities as a map, so that a missing line reads beside the reasons rather than
     *  as a place in a list. */
    private static Map<String, String> declaredFrom(List<String> found) {
        Map<String, String> out = new TreeMap<>();
        found.forEach(each -> out.put(each, ""));
        return out;
    }

    /** Every method and field of the compiler whose type names an operator. */
    private static Map<String, String> carriers() {
        Map<String, String> out = new TreeMap<>();
        forEachClass((owner, model) -> {
            for (MethodModel method : model.methods()) {
                String name = method.methodName().stringValue();
                if (method.methodType().stringValue().contains(BIN_OP) && !synthetic(name)) {
                    out.put(owner + "." + name, "");
                }
            }
            for (FieldModel field : model.fields()) {
                String name = field.fieldName().stringValue();
                if (field.fieldType().stringValue().contains(BIN_OP) && !synthetic(name)) {
                    out.put(owner + "#" + name, "");
                }
            }
        });
        return out;
    }

    /** The methods that reach both a comparison's node and an operator on one. */
    private static List<String> bothInOneMethod() {
        List<String> out = new ArrayList<>();
        forEachClass((owner, model) -> {
            for (MethodModel method : model.methods()) {
                boolean node = false;
                boolean operator = false;
                for (java.lang.classfile.CodeElement element
                        : method.code().map(code -> code.elementList()).orElse(List.of())) {
                    if (element instanceof InvokeInstruction call) {
                        node |= call.owner().asInternalName().equals(COMPARISON)
                                && call.name().stringValue().equals("at");
                        operator |= call.owner().asInternalName().equals(BINARY)
                                && call.name().stringValue().equals("op");
                    }
                }
                if (node && operator) {
                    out.add(owner + "." + method.methodName().stringValue());
                }
            }
        });
        out.sort(String::compareTo);
        return out;
    }

    /** The enum's own members and what the compiler generates for a record, neither of which is
     *  anybody holding an operator. */
    private static boolean synthetic(String name) {
        return name.startsWith("<") || name.startsWith("$")
                || name.equals("values") || name.equals("valueOf");
    }

    private interface EachClass {
        void read(String owner, ClassModel model);
    }

    private static void forEachClass(EachClass each) {
        int read = 0;
        try {
            for (Path path : classes()) {
                ClassModel model = ClassFile.of().parse(Files.readAllBytes(path));
                String owner = model.thisClass().asInternalName()
                        .replace('/', '.').replace('$', '.');
                if (owner.equals("souther.compiler.types.BinOp")) {
                    // The operator itself, whose own members are what an enum is made of.
                    continue;
                }
                read++;
                each.read(owner, model);
            }
        } catch (IOException e) {
            throw new java.io.UncheckedIOException(e);
        }
        assertFalse(read == 0, "no compiled class was read at all, so this says nothing");
    }

    private static List<Path> classes() throws IOException {
        Path root = Path.of("target", "classes").toAbsolutePath();
        try (Stream<Path> walk = Files.walk(root)) {
            return new ArrayList<>(walk.filter(p -> p.toString().endsWith(".class")).toList());
        }
    }
}
