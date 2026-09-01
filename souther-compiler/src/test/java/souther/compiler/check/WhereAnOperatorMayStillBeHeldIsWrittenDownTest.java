package souther.compiler.check;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.lang.classfile.ClassFile;
import java.lang.classfile.ClassModel;
import java.lang.classfile.CodeElement;
import java.lang.classfile.FieldModel;
import java.lang.classfile.MethodModel;
import java.lang.classfile.Opcode;
import java.lang.classfile.instruction.FieldInstruction;
import java.lang.classfile.instruction.InvokeInstruction;
import java.lang.classfile.instruction.TypeCheckInstruction;
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
 * Everywhere an operator can be, and what each of them wants one for.
 *
 * <p>Beside {@link AnOperatorIsAskedWhatItPlacesInOnePlaceTest}, which says how often an operator
 * may be read for what it places and how often a relation may be written as one. That one holds the
 * two crossings between how a comparison is written and what it means to one call each; this one is
 * the ground they stand on, so that an operator reaching somewhere new is a line that has to be
 * written down and given a reason.
 *
 * <p><b>Two ways and no third.</b> An operator is in a method because it was handed in — which is
 * what a signature says — or because it was fetched: answered by a call, read out of a field, or
 * named as one of the constants. Every reading of an operator anywhere begins with one of those,
 * and there is no other way to come by one, so the two lists below are the whole of where an
 * operator can be.
 *
 * <p><b>And nothing here works out what was done with it.</b> A switch, a constant compared
 * against, a set asked for membership and a map asked for an answer are four spellings of one act,
 * and a check that knew three of them would be a check somebody could write the fourth past. So
 * what is fixed is the having, which is an instruction and a descriptor, and what each holder does
 * with it is the reason written beside it.
 *
 * <p>Which puts the copiers in the list. A pass that rebuilds a tree fetches every operator it
 * meets and writes each one into the node it is making, and there is nothing to say about that
 * beyond saying it — a line reading "copies it into the node it is rebuilding" is a line anyone who
 * made it do more would have to edit.
 *
 * <p><b>Lists and not counts.</b> A number stays right while one line goes and another arrives, and
 * the arriving one is exactly what these are for.
 */
class WhereAnOperatorMayStillBeHeldIsWrittenDownTest {

    private static final String BIN_OP = "Lsouther/compiler/types/BinOp;";

    /** Something that has an operator, and what it has one for. */
    private record Held(String what, String why) { }

    /**
     * What is handed an operator: a field it is stored in, and a method a caller passes one to.
     *
     * <p>Written {@code owner#field} and {@code owner.method}.
     */
    private static final List<Held> HANDED_IN = List.of(
            new Held("souther.compiler.ast.Hir.Binary#op",
                    "the resolved tree, which is where an operator is written down"),
            new Held("souther.compiler.core.Core.Binary#op",
                    "the tree a check produces, which carries what the source wrote"),

            new Held("souther.compiler.check.ComparisonPlacement.of",
                    "the one reading of an operator for what it places"),

            new Held("souther.compiler.check.ArithmeticCheck.of",
                    "which operands an operator takes and what it answers, which is a question"
                            + " about the operator itself"),
            new Held("souther.compiler.check.BinaryElaborator.operandBeside",
                    "what the operator asks of one operand, given the one beside it"),
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

            new Held("souther.compiler.semantics.Arithmetic.TheOperator#op",
                    "a library operation declared to compute what an operator computes"),
            new Held("souther.compiler.semantics.NumericResult.TheOtherCaseWhen#op",
                    "a library fact stating the case an operation answers something else in, as a"
                            + " comparison against a number: an operator standing for what it"
                            + " means, in a table nothing recognises a comparison out of"),

            new Held("souther.compiler.check.NumericMeaning.Operator#op",
                    "an arithmetic expression keyed by the operator written in it"),
            new Held("souther.compiler.check.Terms.written",
                    "makes the term a written binary is, off the operator it was written with"),
            new Held("souther.compiler.check.Term.Interner.operator",
                    "which of the canonical terms a comparison is: the same six-into-three the"
                            + " reading of a guard now takes from what was placed, kept here in the"
                            + " operator's own words"),
            new Held("souther.compiler.coverage.SourceOutcome.Compared#op",
                    "the operator an outcome was written with, which is what a report shows"));

    /** What fetches an operator: answered by a call, read out of a field, or named as a constant. */
    private static final List<Held> FETCHED = List.of(
            // Recognising a comparison, which is what carries the claim to everything below.
            new Held("souther.compiler.check.Comparison.of",
                    "asks what the operator places, for a binary of a checked body"),
            new Held("souther.compiler.check.ClauseComparison.of",
                    "the same, for a clause of a data"),
            new Held("souther.compiler.inputs.ComparedNumber.of",
                    "the same, for any binary a walk over the input space met"),
            new Held("souther.compiler.check.Conditions.asOrderComparison",
                    "takes back the operator a composed comparison is written with, which is the"
                            + " one place a relation becomes one"),

            // Rebuilding a tree, which carries the operator across unchanged.
            new Held("souther.compiler.ast.Hir.atSlots",
                    "copies it into the node it is rebuilding"),
            new Held("souther.compiler.ast.Hir.withRegion", "the same, under a region"),
            new Held("souther.compiler.core.Core.atSlots",
                    "copies it into the node it is rebuilding"),
            new Held("souther.compiler.core.Core.withoutItsPlace",
                    "the same, with what said where a node stood taken off"),
            new Held("souther.compiler.check.HelperInliner.inline",
                    "copies it into the node a spliced helper becomes"),
            new Held("souther.compiler.check.HelperInliner.rename",
                    "the same, under a renaming of what the body bound"),
            new Held("souther.compiler.check.NewtypeDesugar.go",
                    "copies it into the node a newtype's rule becomes"),
            new Held("souther.compiler.check.BinaryElaborator.arithmetic",
                    "writes it into the checked node, and into the one inside a construction where"
                            + " the answer is a newtype"),
            new Held("souther.compiler.check.Terms.asWrittenValue",
                    "writes it back into the syntax a value is rendered as"),
            new Held("souther.compiler.check.Resolve.expr",
                    "translates the parsed tree's own operator into this one, by the name each is"
                            + " spelled with: two enums held together by a string rather than by"
                            + " anything that would fail to compile"),

            // Handing it on to something that answers about it.
            new Held("souther.compiler.check.HelperParams.BodyTyping.visit",
                    "hands it to what types an operand standing beside it"),
            new Held("souther.compiler.check.Terms.numericMeaningOf",
                    "asks whether it computes a number, and keys the meaning by it"),
            new Held("souther.compiler.check.Terms.namedByRule", "asks whether it computes a number"),
            new Held("souther.compiler.check.Terms.lambda$naming$1",
                    "hands it to the interner, which says which canonical term the comparison is"),
            new Held("souther.compiler.check.Terms.asOperator",
                    "reads the operator an arithmetic meaning was keyed by"),
            new Held("souther.compiler.check.Terms.theOneOf", "the same, for the meaning it interns"),
            new Held("souther.compiler.check.Terms.openedKey", "the same, for the term it keys"),
            new Held("souther.compiler.check.Terms.recipeFor", "the same, for the recipe it names"),
            new Held("souther.compiler.check.NumericMeanings.of",
                    "keys an arithmetic meaning by the operator a library operation computes"),
            new Held("souther.compiler.check.DischargeRules.formOperations",
                    "asks which operator a library operation is defined as"),
            new Held("souther.compiler.coverage.CoverageSites.Walk.number",
                    "records the operator an outcome was written with, which is what a report shows"),
            new Held("souther.compiler.report.ArmVocabulary.label",
                    "writes the operator into the words a report shows for an arm"),
            new Held("souther.compiler.reading.Meetings.run",
                    "gathers the operands one operator reaches, which is what it is asked about"),
            new Held("souther.compiler.check.PathReachability.unanswered",
                    "names the operator in what it says went unanswered"),
            new Held("souther.compiler.check.TheOtherCase.conditionAt",
                    "composes the comparison a library fact states its other case by, out of the"
                            + " operator that fact holds: what is written there is read back as a"
                            + " comparison by everything downstream, and nothing recognised it"),

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
                    "asks the enum whether the operator stops early"),

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

            // And whether it compares at all, asked of the one place that says so.
            new Held("souther.compiler.check.InvariantChecker.arithmeticOf",
                    "asks the enum whether the operator compares, which its caller has now"
                            + " recognised the comparison for as well"),
            new Held("souther.compiler.check.Predicates.atomsNamedBy",
                    "asks the enum whether the operator compares: both sides of a comparison are"
                            + " named whatever it states, and anything else is the one value it is"),
            new Held("souther.compiler.check.Relates.twoPositions",
                    "asks the enum whether the operator compares, for a rule that stands one"
                            + " position against another"),

            // Handing back the operator a value of one's own holds.
            new Held("souther.compiler.ast.Hir.Binary.op", "hands back what the node holds"),
            new Held("souther.compiler.core.Core.Binary.op", "hands back what the node holds"),
            new Held("souther.compiler.check.NumericMeaning.Operator.op",
                    "hands back the operator an arithmetic meaning is keyed by"),
            new Held("souther.compiler.coverage.SourceOutcome.Compared.op",
                    "hands back the operator an outcome was written with"),
            new Held("souther.compiler.semantics.Arithmetic.TheOperator.op",
                    "hands back the operator a library operation computes"),
            new Held("souther.compiler.semantics.NumericResult.TheOtherCaseWhen.op",
                    "hands back the operator a library fact states its other case by"),
            new Held("souther.compiler.check.DischargeRules.operator",
                    "reads the operator a library operation is declared to compute"),

            // Naming a constant, which is the other way to come by one.
            new Held("souther.compiler.check.ComparisonWriting.operatorStating",
                    "names the constant a relation is written as, which is the one place a"
                            + " composed comparison is said in the language's own operators"),
            new Held("souther.compiler.check.Conditions.asSizeComparison",
                    "writes the equality an emptiness check means: a size stood against nought"),
            new Held("souther.compiler.check.Conditions.canonical",
                    "writes the two comparisons a fact is keyed by, which what was placed says"
                            + " which of and which way round"),
            new Held("souther.compiler.check.Terms.repeating",
                    "writes the multiplication a repeated accumulation comes to"),
            new Held("souther.compiler.semantics.OperationFacts.declared",
                    "the library's own table, naming the operator each arithmetic operation"
                            + " computes"),
            new Held("souther.compiler.semantics.OperationFacts.computesInTheCaseCarrying",
                    "the same, for an operation whose other case is stated as a comparison"),
            new Held("souther.compiler.check.ArithmeticCheck.of",
                    "names the constants it has rules for, against the operator it was handed"),
            new Held("souther.compiler.check.BinaryElaborator.operandBeside",
                    "names the two that take truths and the two that scale a newtype"),
            new Held("souther.compiler.check.Terms.isArith",
                    "names the four constants it calls arithmetic, which is a membership the enum"
                            + " does not own"),
            new Held("souther.compiler.partition.Condition.combines",
                    "names the two constants it calls joining, which is a membership the enum"
                            + " already answers for under another name"),
            new Held("souther.compiler.check.Term.Interner.operator",
                    "names the constants the canonical terms are keyed by, which is the"
                            + " six-into-three the reading of a guard now takes from what was"
                            + " placed"));

    @Test
    void everythingHandedAnOperatorIsWrittenDownWithAReason() {
        assertEquals(declared(HANDED_IN), found(handedAnOperator()),
                "an operator handed somewhere new is a line to be written here with what it is"
                        + " wanted for. What each of these is handed one for: " + why(HANDED_IN));
    }

    @Test
    void everythingFetchingAnOperatorIsWrittenDownWithAReason() {
        assertEquals(declared(FETCHED), found(fetchesAnOperator()),
                "an operator fetched somewhere new is a line to be written here with what is done"
                        + " with it. What each of these fetches one for: " + why(FETCHED));
    }

    /** Every field whose type is an operator, and every method whose signature names one. */
    private static List<String> handedAnOperator() {
        List<String> out = new ArrayList<>();
        forEachClass((owner, model) -> {
            for (MethodModel method : model.methods()) {
                String name = method.methodName().stringValue();
                // What it is given, and not what it answers: a method answering an operator got one
                // from somewhere, which is the other list.
                if (method.methodTypeSymbol().parameterList().stream()
                        .anyMatch(each -> each.descriptorString().equals(BIN_OP))
                        && !generated(name)) {
                    out.add(owner + "." + name);
                }
            }
            for (FieldModel field : model.fields()) {
                String name = field.fieldName().stringValue();
                if (field.fieldType().stringValue().contains(BIN_OP) && !generated(name)) {
                    out.add(owner + "#" + name);
                }
            }
        });
        return out;
    }

    /**
     * Every method in which an operator arrives without being handed in: answered by a call, read
     * out of a field, or named as a constant.
     *
     * <p>The three instructions that put one on the stack, which is the whole of how a method comes
     * by an operator it was not given.
     */
    private static List<String> fetchesAnOperator() {
        List<String> out = new ArrayList<>();
        forEachClass((owner, model) -> {
            for (MethodModel method : model.methods()) {
                boolean fetches = false;
                for (CodeElement element
                        : method.code().map(code -> code.elementList()).orElse(List.of())) {
                    if (element instanceof InvokeInstruction call) {
                        fetches |= names(call.typeSymbol().returnType().descriptorString());
                    }
                    if (element instanceof FieldInstruction field) {
                        fetches |= names(field.typeSymbol().descriptorString());
                    }
                    // What a collection or anything else generic hands back is an Object until it
                    // is cast, so the cast is where the operator arrives — and a table held in a
                    // Map is exactly that.
                    if (element instanceof TypeCheckInstruction cast
                            && cast.opcode() == Opcode.CHECKCAST) {
                        fetches |= names("L" + cast.type().asInternalName() + ";")
                                || names(cast.type().asInternalName());
                    }
                }
                if (fetches && !generated(method.methodName().stringValue())) {
                    out.add(owner + "." + method.methodName().stringValue());
                }
            }
        });
        return out;
    }

    /** Whether a descriptor names an operator, an array of them included: what {@code values()}
     *  hands back is an array, and an operator taken out of one arrived with it. */
    private static boolean names(String descriptor) {
        return descriptor.contains(BIN_OP) || descriptor.equals("souther/compiler/types/BinOp");
    }

    /** A constructor, a class's own setting up, and what the compiler writes for an enum: none of
     *  them anybody holding an operator. */
    private static boolean generated(String name) {
        return name.startsWith("<") || name.startsWith("$")
                || name.equals("values") || name.equals("valueOf");
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

    /** What was found, as a map, so that a missing line reads beside the reasons rather than as a
     *  place in a list. */
    private static Map<String, String> found(List<String> what) {
        Map<String, String> out = new TreeMap<>();
        what.forEach(each -> out.put(each, ""));
        return out;
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
