package souther.compiler.report;

import souther.compiler.publish.MaterialisationRegionWord;
import souther.compiler.publish.RegionSlotWord;
import souther.compiler.publish.ThroughStepWord;
import souther.compiler.types.ExpansionSite;
import souther.compiler.types.MaterialisationSite;
import souther.compiler.types.RegionSlot;
import souther.compiler.types.StepOfACopy;
import souther.compiler.types.WrittenOwner;

import tools.jackson.databind.node.ArrayNode;
import tools.jackson.databind.node.ObjectNode;

import java.util.ArrayList;
import java.util.List;

import static souther.compiler.report.AdequacyReport.word;

/**
 * What tells one step of a copy from every other, said once and written two ways.
 *
 * <p>Which fields identify a step is decided here and nowhere else. A document writes them as
 * fields of the step, and a page writes them as words where it has no place to send a reader; two
 * selections would be free to differ, and the page would then call two steps by one name that the
 * document tells apart.
 *
 * <p>Every field a step's identity has, each as what it is. A call is told by the call written in a
 * definition; a name written where a value goes by the reference; a block handed over by the copy
 * it was handed to, the parameter it filled and where it was applied; a build by the region it was
 * made for. Nothing is written as a string made for this compiler's own reading.
 */
final class StepIdentity {

    /** Where the fields are put, which is the one thing the two writings differ in. */
    interface Fields {

        void put(String field, String value);

        void put(String field, int value);

        /** The cases a slot of a {@code match} is for, the one field of a step that is a list. */
        void cases(List<String> names);

        /** The fields of {@code field}, which is itself identified by fields. */
        Fields within(String field);
    }

    /** Every field of {@code step}. */
    static void of(Fields into, StepOfACopy step) {
        switch (step) {
            case StepOfACopy.ACall(var called, var at) -> {
                into.put("kind", word(ThroughStepWord.EXPANSION));
                into.put("expanded", called.toString());
                site(into, at);
            }
            case StepOfACopy.ABuild(var built, var region) -> {
                into.put("kind", word(ThroughStepWord.MATERIALISATION));
                into.put("materialised", built.toString());
                region(into.within("at"), region);
            }
        }
    }

    /**
     * Where a copy was made: a call by the call written in a definition, a name by the reference,
     * and a block handed over by what it was handed to, which parameter it filled and where it was
     * applied — the copy it was handed to identified the way a step is.
     */
    private static void site(Fields into, ExpansionSite at) {
        switch (at) {
            case ExpansionSite.Written(var call) -> {
                into.put("module", call.owner().module());
                into.put("definition", WrittenOwner.theBodyThatWrote(call.owner()).definition());
                into.put("call", call.ordinal());
                into.put("lowered", call.lowered());
            }
            case ExpansionSite.Named(var reference) -> {
                Fields named = into.within("name");
                named.put("module", reference.owner().module());
                named.put("definition",
                        WrittenOwner.theBodyThatWrote(reference.owner()).definition());
                named.put("reference", reference.ordinal());
            }
            case ExpansionSite.Supplied supplied -> {
                Fields handed = into.within("supplied");
                Fields to = handed.within("handedTo");
                to.put("expanded", supplied.copy().expanded().toString());
                site(to, supplied.copy().at());
                handed.put("parameter", supplied.from().parameter().index());
                site(handed.within("appliedAt"), supplied.application());
            }
        }
    }

    /** The region a build was made for, in the words the source settles it by. */
    static void region(Fields into, MaterialisationSite site) {
        switch (site) {
            case MaterialisationSite.Body body -> {
                into.put("kind", word(MaterialisationRegionWord.BODY));
                into.put("module", body.owner().module());
                into.put("definition", body.owner().definition());
            }
            case MaterialisationSite.Slot slot -> {
                into.put("kind", word(MaterialisationRegionWord.SLOT));
                into.put("module", slot.construct().owner().module());
                into.put("definition",
                        WrittenOwner.theBodyThatWrote(slot.construct().owner()).definition());
                into.put("construct", slot.construct().ordinal());
                into.put("lowered", slot.construct().lowered());
                switch (slot.slot()) {
                    case RegionSlot.IfThen _ -> into.put("slot", word(RegionSlotWord.IF_THEN));
                    case RegionSlot.IfElse _ -> into.put("slot", word(RegionSlotWord.IF_ELSE));
                    case RegionSlot.ConstructedThen _ ->
                            into.put("slot", word(RegionSlotWord.CONSTRUCTED_THEN));
                    case RegionSlot.ConstructedElse refused -> {
                        into.put("slot", word(RegionSlotWord.CONSTRUCTED_ELSE));
                        refused.clause().ifPresent(clause -> into.put("clause", clause));
                    }
                    case RegionSlot.MatchCase match -> {
                        into.put("slot", word(RegionSlotWord.MATCH_CASE));
                        into.cases(match.caseTypes());
                    }
                    case RegionSlot.ShortCircuitRight _ ->
                            into.put("slot", word(RegionSlotWord.SHORT_CIRCUIT_RIGHT));
                    case RegionSlot.ComprehensionElement _ ->
                            into.put("slot", word(RegionSlotWord.COMPREHENSION_ELEMENT));
                    case RegionSlot.ComprehensionGuard guard -> {
                        into.put("slot", word(RegionSlotWord.COMPREHENSION_GUARD));
                        into.put("index", guard.index());
                    }
                }
            }
            case MaterialisationSite.WrittenBlock block -> {
                into.put("kind", word(MaterialisationRegionWord.BLOCK));
                into.put("module", block.rule().owner().module());
                into.put("definition",
                        WrittenOwner.theBodyThatWrote(block.rule().owner()).definition());
                into.put("rule", block.rule().ordinal());
            }
            case MaterialisationSite.GeneratedBlock block -> {
                into.put("kind", word(MaterialisationRegionWord.BLOCK_OF_NAME));
                into.put("module", block.reference().owner().module());
                into.put("definition",
                        WrittenOwner.theBodyThatWrote(block.reference().owner()).definition());
                into.put("reference", block.reference().ordinal());
            }
            case MaterialisationSite.Invariant invariant -> {
                into.put("kind", word(MaterialisationRegionWord.INVARIANT));
                into.put("module", invariant.declaration().module());
                into.put("declaration", invariant.declaration().declaration().name());
                into.put("ordinal", invariant.ordinal());
            }
            case MaterialisationSite.Ensures ensures -> {
                into.put("kind", word(MaterialisationRegionWord.ENSURES));
                into.put("module", ensures.stated().module());
                into.put("definition", ensures.stated().behavior());
                into.put("ordinal", ensures.clause());
                into.put("arm", ensures.arm());
            }
        }
    }

    /** The fields as a document writes them. */
    record InTheDocument(ObjectNode node) implements Fields {

        @Override
        public void put(String field, String value) {
            node.put(field, value);
        }

        @Override
        public void put(String field, int value) {
            node.put(field, value);
        }

        @Override
        public void cases(List<String> names) {
            ArrayNode all = node.putArray("cases");
            names.forEach(all::add);
        }

        @Override
        public Fields within(String field) {
            return new InTheDocument(node.putObject(field));
        }
    }

    /** The fields as a page writes them: each by its name, in the order they are put, and a field
     *  identified by fields in brackets after its name. */
    static final class InWords implements Fields {

        private final List<Object> said = new ArrayList<>();

        @Override
        public void put(String field, String value) {
            said.add(field + " " + value);
        }

        @Override
        public void put(String field, int value) {
            said.add(field + " " + value);
        }

        @Override
        public void cases(List<String> names) {
            said.add("cases " + String.join(" | ", names));
        }

        @Override
        public Fields within(String field) {
            InWords inner = new InWords();
            said.add(new Within(field, inner));
            return inner;
        }

        private record Within(String field, InWords fields) {

            @Override
            public String toString() {
                return field + " (" + fields + ")";
            }
        }

        @Override
        public String toString() {
            return String.join(", ", said.stream().map(String::valueOf).toList());
        }
    }

    /** {@code step} in words, for a page with no place to send a reader to it. */
    static String inWords(StepOfACopy step) {
        InWords words = new InWords();
        of(words, step);
        return words.toString();
    }

    private StepIdentity() {}
}
