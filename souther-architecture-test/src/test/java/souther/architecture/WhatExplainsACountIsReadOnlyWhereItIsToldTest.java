package souther.architecture;

import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassModel;
import java.lang.classfile.CodeElement;
import java.lang.classfile.CodeModel;
import java.lang.classfile.FieldModel;
import java.lang.classfile.MethodModel;
import java.lang.classfile.instruction.FieldInstruction;
import java.lang.classfile.instruction.InvokeInstruction;
import java.nio.file.Path;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Who reads what a value carries only to tell an author what multiplied the cases of a line, or
 * which applications of a closure a reading of a line was read on.
 *
 * <p>Which call handed a closure its parameter, which application of it a statement was read on,
 * how the statement was derived on each, how many ways each case asked stood for, and which
 * applications drew a line: none of these decides what a body states or which rows a line asks
 * for. Which call handed what is read off the
 * applications a body's bindings already hold, and is no part of them. The rest are carried inside
 * the values a reading is made of — an application, a derivation, an assessment — and so are part
 * of what makes two of those values equal. That is on purpose. A value left equal to one carrying
 * another account of where it came from would let a cache hand the first account out for the
 * second, and an author would be told what multiplied a line by a call that never made it.
 *
 * <p>What equality cannot say is that the account is nothing more. That is held here: each is read
 * outside the type that carries it by the methods written below and by none other, each of which
 * either hands it on to the next carrier or tells it. A method reading one to decide something
 * would be a row this list does not have.
 *
 * <p>Read off the compiled classes, field reads and calls alike, since a class in the same file
 * reads the field. A record pattern calls every accessor of the record it takes apart, so taking
 * one of these apart is a read and a row.
 */
class WhatExplainsACountIsReadOnlyWhereItIsToldTest {

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    /** A component a value carries for an author's sake: its type, and its name. */
    private record Account(String owner, String name) {}

    private static final Account WRITTEN_CALL_OF_A_USE =
            new Account("souther/compiler/check/ClosureUses$Application", "written");
    private static final Account HANDED_BY_A_BODY =
            new Account("souther/compiler/check/ElementBindings", "handedBy");
    private static final Account HANDED_BY_AN_ENVIRONMENT =
            new Account("souther/compiler/inputs/BindingEnvironment", "handedBy");
    private static final Account MADE_BY_AN_APPLICATION =
            new Account("souther/compiler/partition/ClosureApplications$Application", "madeBy");
    private static final Account MADE_BY_A_DERIVATION =
            new Account("souther/compiler/meaning/Derivation$AnApplication", "madeBy");
    private static final Account ORDINAL_OF_A_DERIVATION =
            new Account("souther/compiler/meaning/Derivation$AnApplication", "ordinal");
    private static final Account DERIVED_BY_THE_LINES_DRAWN =
            new Account("souther/compiler/partition/Cutting$Read$Several", "derivedBy");
    private static final Account DERIVED_BY_THE_LINES_ASSESSED =
            new Account("souther/compiler/partition/ComparisonAssessment$Several", "derivedBy");
    private static final Account EXPANDED_OF_A_LINE =
            new Account("souther/compiler/partition/ComparisonAssessment$Several$Part",
                    "expanded");
    private static final Account COUNTED_OF_A_LINE =
            new Account("souther/compiler/meaning/CasesOfALineAsked$NotWorkedOut", "counted");
    private static final Account READ_ON_BY_A_LINE =
            new Account("souther/compiler/partition/Cutting", "readOn");
    private static final Account READ_ON_BY_A_RELATION =
            new Account("souther/compiler/partition/Cutting$Read$AgainstAnotherValue", "readOn");
    private static final Account READ_ON_BESIDE_A_RELATION =
            new Account("souther/compiler/partition/ComparisonAssessment$DrawnBeside", "readOn");
    private static final Account READ_ON_BY_AN_ORIGIN =
            new Account("souther/compiler/partition/LineOrigin$ComparisonOrigin$Read", "readOn");
    private static final Account READ_ON_BY_A_READING =
            new Account("souther/compiler/query/BorderAssessment", "readOn");

    /**
     * Every method outside its carrier that reads each account.
     *
     * <p>Which call made an application of a closure is read by the body's bindings, for the calls
     * that handed one of its parameters; which calls those are is asked of an environment, and the
     * environment asks the bindings; the closure's reading asks it once, at the block, for the one
     * call that made its applications. Which application a derivation was made on is read where the
     * choices a case is made of are told apart. The statement's derivations are handed from the
     * lines drawn to the lines assessed as they are made; the counts are put beside the line where
     * its parts are narrowed, and told where the assessment says what each line was told. The
     * application a reading is inside, and the derivations an assessment holds, are read by their
     * carrier alone, which is where they are handed on.
     *
     * <p>The applications a line was drawn on are handed from the line to the lines parting the
     * values that settle it and to the line's origin; from a relation to what those lines are drawn
     * beside, and from there to each of them; from the origin to its reading, which puts them
     * together where the readings of one line are put together and is told where an obligation's
     * readings are written, and where the calls they name are placed.
     */
    private static final Map<Account, Set<String>> READ_BY = expected();

    private static Map<Account, Set<String>> expected() {
        Map<Account, Set<String>> by = new LinkedHashMap<>();
        by.put(WRITTEN_CALL_OF_A_USE, Set.of(AMethod.of("souther/compiler/check/ElementBindings",
                "handedBy", "(Lsouther/compiler/types/BindingId;)Ljava/util/Set;")));
        by.put(HANDED_BY_A_BODY, Set.of(AMethod.of("souther/compiler/inputs/BindingEnvironment",
                "handedBy", "(Lsouther/compiler/types/BindingId;)Ljava/util/Set;")));
        by.put(HANDED_BY_AN_ENVIRONMENT, Set.of(AMethod.of("souther/compiler/inputs/InputReads",
                "handingCall", "(Lsouther/compiler/core/Core$Block;)Ljava/util/Optional;")));
        by.put(MADE_BY_AN_APPLICATION, Set.of());
        String choices = AMethod.of("souther/compiler/meaning/TheChoicesACaseIsMadeOf$Reading",
                "visit", "(Lsouther/compiler/meaning/Derivation;"
                        + "Lsouther/compiler/meaning/TheChoicesACaseIsMadeOf$Context;)Z");
        by.put(MADE_BY_A_DERIVATION, Set.of(choices));
        by.put(ORDINAL_OF_A_DERIVATION, Set.of(choices));
        by.put(DERIVED_BY_THE_LINES_DRAWN, Set.of(AMethod.of(
                "souther/compiler/partition/ComparisonAssessment", "eachLineOf",
                "(Ljava/lang/String;Ljava/util/Optional;"
                        + "Lsouther/compiler/partition/Cutting$Read$Several;"
                        + "Lsouther/compiler/diag/Citation;Lsouther/compiler/inputs/InputReading;Z"
                        + "Ljava/util/function/Supplier;"
                        + "Lsouther/compiler/partition/CountWitnesses$Lookup;)"
                        + "Lsouther/compiler/partition/ComparisonAssessment;")));
        by.put(DERIVED_BY_THE_LINES_ASSESSED, Set.of());
        by.put(EXPANDED_OF_A_LINE, Set.of(AMethod.of(
                "souther/compiler/partition/ComparisonAssessment$Several", "caseExpansions",
                "()Ljava/util/List;")));
        by.put(COUNTED_OF_A_LINE, Set.of(AMethod.of(
                "souther/compiler/partition/ComparisonAssessment", "aPartNarrowed",
                "(Lsouther/compiler/partition/ComparisonAssessment$Several$Part;"
                        + "Lsouther/compiler/partition/Reachability;"
                        + "Lsouther/compiler/partition/WaysToACase;Ljava/util/List;Z"
                        + "Lsouther/compiler/inputs/InputReading;"
                        + "Lsouther/compiler/partition/CountWitnesses$Lookup;)Ljava/util/List;")));
        String settling = AMethod.of("souther/compiler/partition/ComparisonAssessment",
                "settlingLines", "(Lsouther/compiler/partition/ComparisonAssessment$DrawnBeside;"
                        + "Ljava/util/Map;Lsouther/compiler/inputs/InputReading;"
                        + "Lsouther/compiler/partition/CountWitnesses$Lookup;)Ljava/util/List;");
        by.put(READ_ON_BY_A_LINE, Set.of(
                AMethod.of("souther/compiler/partition/ComparisonAssessment$AcrossPositions",
                        "leaving", "(Lsouther/compiler/partition/Cutting;"
                                + "Lsouther/compiler/diag/Citation;"
                                + "Lsouther/compiler/partition/ComparisonAssessment$Places;"
                                + "Lsouther/compiler/partition/UndividedByARelation;"
                                + "Lsouther/compiler/partition/UndividedByARelation$WhatItLeaves;"
                                + "Lsouther/compiler/meaning/AuthoredPointMapping;"
                                + "Lsouther/compiler/inputs/InputReading;"
                                + "Lsouther/compiler/partition/CountWitnesses$Lookup;)"
                                + "Lsouther/compiler/partition/ComparisonAssessment$AcrossPositions;"),
                AMethod.of("souther/compiler/partition/GuardThresholds", "originOf",
                        "(Ljava/lang/String;Lsouther/compiler/types/ModelOccurrence;"
                                + "Lsouther/compiler/coverage/EmittedComparisonState$Instrumented;"
                                + "Lsouther/compiler/types/SourceConstructOrigin;"
                                + "Lsouther/compiler/check/RuleReportAnchor;"
                                + "Lsouther/compiler/partition/ElementsMetOn;Ljava/util/Optional;"
                                + "Lsouther/compiler/partition/Cutting;"
                                + "Lsouther/compiler/meaning/AuthoredPointMapping;)"
                                + "Lsouther/compiler/partition/LineOrigin$ComparisonOrigin;")));
        by.put(READ_ON_BY_A_RELATION, Set.of(AMethod.of(
                "souther/compiler/partition/ComparisonAssessment$AgainstAnotherValue", "of",
                "(Lsouther/compiler/partition/Cutting$Read$AgainstAnotherValue;"
                        + "Lsouther/compiler/inputs/InputReading;Ljava/util/Optional;"
                        + "Lsouther/compiler/partition/CountWitnesses$Lookup;)"
                        + "Lsouther/compiler/partition/ComparisonAssessment$AgainstAnotherValue;")));
        by.put(READ_ON_BESIDE_A_RELATION, Set.of(settling));
        by.put(READ_ON_BY_AN_ORIGIN, Set.of(AMethod.of("souther/compiler/partition/LineOrigin",
                "readOn", "()Lsouther/compiler/types/ApplicationsReadOn;")));
        by.put(READ_ON_BY_A_READING, Set.of(
                AMethod.of("souther/compiler/query/Coverages", "asOneLine",
                        "(Ljava/util/List;)Lsouther/compiler/query/BorderAssessment;"),
                AMethod.of("souther/compiler/query/Coverages", "asOneLine",
                        "(Lsouther/compiler/query/BorderAssessment;"
                                + "Lsouther/compiler/query/BorderAssessment;)"
                                + "Lsouther/compiler/query/BorderAssessment;"),
                AMethod.of("souther/compiler/query/Coverages", "searched",
                        "(Lsouther/compiler/query/LineReadings;"
                                + "Lsouther/compiler/partition/MeasuredInput;"
                                + "Lsouther/compiler/query/Coverages$Probe;"
                                + "Lsouther/compiler/partition/ReachingCuts;Ljava/util/Set;)"
                                + "Lsouther/compiler/query/LineReadings;"),
                AMethod.of("souther/compiler/report/AdequacyReport", "obligations",
                        "(Lsouther/compiler/publish/DocumentArray;Ljava/util/List;Ljava/util/Map;"
                                + "Lsouther/compiler/report/DocumentSources;"
                                + "Lsouther/compiler/publish/PublishedRuleHandle$WhereARuleIs;"
                                + "Lsouther/compiler/report/AdequacyReport$WhereARowIs;"
                                + "Ljava/util/Optional;)V"),
                AMethod.of("souther/compiler/report/AdequacyReport", "partPlaces",
                        "(Lsouther/compiler/query/Compilation;"
                                + "Lsouther/compiler/query/PartitionEvidence;Ljava/util/List;"
                                + "Ljava/util/List;)Ljava/util/Map;")));
        return by;
    }

    /**
     * What the compiled classes say of every account: who reads it outside its carrier, whether
     * its carrier reads it, and the carrier.
     *
     * <p>Read off in one walk over every method's code, which is the whole of what either test
     * costs: each instruction is matched against every account at once, so a row added to the list
     * adds a lookup and not a walk.
     */
    private record Walked(Map<Account, Set<String>> outside, Set<Account> inside,
                          Map<Account, ClassModel> carriers) {}

    private static final Walked WALKED = walked();

    private static Walked walked() {
        Map<Account, Set<String>> outside = new LinkedHashMap<>();
        READ_BY.keySet().forEach(account -> outside.put(account, new TreeSet<>()));
        Set<Account> inside = new HashSet<>();
        Map<Account, ClassModel> carriers = new HashMap<>();
        for (Path module : COMPILED.modules()) {
            for (ClassModel each : COMPILED.classesOf(module)) {
                String owner = each.thisClass().asInternalName();
                READ_BY.keySet().stream().filter(account -> account.owner().equals(owner))
                        .forEach(account -> carriers.put(account, each));
                for (MethodModel method : each.methods()) {
                    CodeModel code = method.code().orElse(null);
                    if (code == null) {
                        continue;
                    }
                    for (CodeElement element : code) {
                        Account read = switch (element) {
                            case FieldInstruction it -> new Account(
                                    it.owner().name().stringValue(), it.name().stringValue());
                            case InvokeInstruction it -> new Account(
                                    it.owner().name().stringValue(), it.name().stringValue());
                            default -> null;
                        };
                        if (read == null || !outside.containsKey(read)) {
                            continue;
                        }
                        if (read.owner().equals(owner)) {
                            inside.add(read);
                        } else {
                            outside.get(read).add(AMethod.of(each, method));
                        }
                    }
                }
            }
        }
        return new Walked(outside, inside, carriers);
    }

    @Test
    void eachAccountIsReadOnlyWhereItIsHandedOnOrTold() {
        assertEquals(sorted(READ_BY), WALKED.outside(),
                "what a value carries to tell an author what multiplied a line is read to decide"
                        + " nothing: a reader not written here is one that may");
    }

    /**
     * And the walk sees each account where it is: every one is something its carrier declares,
     * and read somewhere, its carrier included. Matched on a name nothing has, every row would be
     * absent and the list above equal to itself.
     */
    @Test
    void andEachAccountIsAComponentTheWalkSeesBeingRead() {
        for (Account account : READ_BY.keySet()) {
            assertTrue(declares(account), account + " is declared by its carrier");
            assertTrue(!WALKED.outside().get(account).isEmpty()
                            || WALKED.inside().contains(account),
                    account + " is read somewhere, or the walk sees no read of it at all");
        }
    }

    private static Map<Account, Set<String>> sorted(Map<Account, Set<String>> by) {
        Map<Account, Set<String>> sorted = new LinkedHashMap<>();
        by.forEach((account, readers) -> sorted.put(account, new TreeSet<>(readers)));
        return sorted;
    }

    /** Whether the carrier holds the account as a field, or works it out in a method. */
    private static boolean declares(Account account) {
        ClassModel carrier = WALKED.carriers().get(account);
        if (carrier == null) {
            throw new AssertionError(account.owner() + " is compiled in no module");
        }
        return carrier.fields().stream().map(FieldModel::fieldName)
                .anyMatch(name -> name.equalsString(account.name()))
                || carrier.methods().stream().map(MethodModel::methodName)
                        .anyMatch(name -> name.equalsString(account.name()));
    }
}
