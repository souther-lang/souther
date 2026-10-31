package souther.architecture;

import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassModel;
import java.lang.classfile.MethodModel;
import java.lang.classfile.instruction.InvokeInstruction;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What a run works out before a comparison is told only by the walk of what it works out, one node
 * at a time as the walk reaches it, under the application of a closure the walk is reading.
 *
 * <p>A reading of what a value comes to reads parts no run need work out: the body of a closure on
 * an element it is handed, the arms a value may be one of, an attempt that stops halfway. Told from
 * there, an operator of one application is taken for one every run makes, and one the walk then
 * reads no form of on another application is taken as said for all of them — a run that stops there
 * is read as getting past. So the readings of values tell nothing, and every telling is one of the
 * walk's methods, each of which is handed the node it tells.
 *
 * <p>Asked of the compiled code: a telling written in a callback of a reading is an invocation as
 * much as one written in the walk.
 */
class WhatARunWorksOutIsToldOnlyByTheWalkOfItTest {

    private static final String PULLBACK = "souther/compiler/partition/Pullback";

    private static final String OPERATORS = PULLBACK + "$Operators";

    private static final String CORE = "Lsouther/compiler/core/Core";

    private static final String READS = "Lsouther/compiler/inputs/InputReads;";

    /** The walk's methods that tell what it reaches. */
    private static final Set<String> THE_WALK = Set.of(
            AMethod.of(PULLBACK, "anOperator", "(" + CORE + ";" + READS + ")V"),
            AMethod.of(PULLBACK, "aConstruction", "(" + CORE + "$Construct;" + READS + ")V"),
            AMethod.of(PULLBACK, "madeOfARounding", "(" + CORE + "$Construct;"
                    + "Lsouther/compiler/check/TypeView;" + READS + ")V"),
            AMethod.of(PULLBACK, "oneOperationOfTheLibrary",
                    "(" + CORE + "$PreservedCall;" + READS + ")V"));

    private static final CompiledOutputs PUBLISHED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    /** Every method outside the record of operators that tells it of one. */
    private static Set<String> whoTells(CompiledOutputs outputs) {
        Set<String> found = new TreeSet<>();
        for (ClassModel owner : outputs.all()) {
            if (owner.thisClass().asInternalName().equals(OPERATORS)) {
                continue;
            }
            WhereALambdaIsWritten lambdas = WhereALambdaIsWritten.in(owner);
            for (MethodModel method : owner.methods()) {
                if (method.code().isEmpty()) {
                    continue;
                }
                for (var element : method.code().orElseThrow()) {
                    if (element instanceof InvokeInstruction call
                            && call.owner().asInternalName().equals(OPERATORS)
                            && call.name().equalsString("tell")) {
                        found.add(lambdas.enclosing(AMethod.of(owner, method)));
                    }
                }
            }
        }
        return found;
    }

    /**
     * Equal and not contained: the walk's methods tell today, so a rule that found none of them
     * would be answering about nothing, and one that finds another has found a reading that tells.
     */
    @Test
    void onlyTheWalkTellsWhatARunWorksOut() {
        assertEquals(new TreeSet<>(THE_WALK), whoTells(PUBLISHED),
                "an operator a run works out is told by the walk of it (Pullback#operatorsIn) at"
                        + " the node it reaches; a reading of a value reads it and tells nothing");
    }
}
