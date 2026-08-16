package souther.compiler.meta;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Compilation;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Output;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * Whether the declarations an answer reads a row's values by are the ones the row is written for.
 *
 * <p>An implementation supplied from outside a compile was built against a module's classes as some
 * earlier build emitted them, and the rows it is held to are read now. Two builds, and nothing makes
 * them one: a project where the model is edited and only the tests are re-run puts them a revision
 * apart as a matter of course. What is asked here is whether they still say the same thing about
 * everything a value crossing between them depends on.
 *
 * <p>The question is not whether the two are the same build. A build differs from another in ways a
 * crossing cannot see — a {@code let} body, an example, the order two declarations were written in —
 * and answering with "not the same build" would report a model as one whose rows do not hold every
 * time anything at all was edited. What is compared is what the crossing depends on.
 */
class TheDeclarationsAnAnswerReadsByAreHeldToTheEvaluatedModuleTest {

    private static final String MODEL = """
            module example.stale
            import String ( length )

            data Title = String
                invariant length(value) > 0

            data Todo = { title: Title, done: Bool }

            behavior rename : (t: Todo, to: Title) -> Todo
                constructs Todo

            let rename (t, to) = Todo { title = to, done = t.done }
            """;

    /** A model spread over two modules: what a field's type is declared by is imported. */
    private static final String SHARED = """
            module example.shared exposing ( Title, Note )
            import String ( length )

            data Title = String
                invariant length(value) > 0

            data Note = String
            """;

    private static final String ROOT = """
            module example.root
            import example.shared ( Title, Note )

            data Todo = { title: Title, note: Note, done: Bool }

            behavior rename : (t: Todo, to: Title) -> Todo
                constructs Todo

            let rename (t, to) = Todo { title = to, note = t.note, done = t.done }
            """;

    /**
     * A module publishing two kinds of helper: one an invariant is read through, and one that is
     * exposed and nothing declares its way to.
     */
    private static final String EXPOSING_MODEL = """
            module example.published exposing ( Title, describe )
            import String ( length, trim )

            data Title = String
                invariant longEnough(value)

            behavior rename : (t: Title) -> Title
                constructs Title

            let longEnough (s: String) : Bool = length(s) > 0

            let describe (t: Title) : String = trim(t.value)

            let rename (t) = Title(t.value)
            """;

    /** The same model reaching the shared type qualified, with no import line at all. */
    private static final String QUALIFYING_ROOT = """
            module example.root

            data Todo = { title: example.shared.Title, done: Bool }

            behavior rename : (t: Todo) -> Todo
                constructs Todo

            let rename (t) = Todo { title = t.title, done = t.done }
            """;

    /** And the same again, reaching it through an alias. */
    private static final String ALIASING_ROOT = """
            module example.root
            import example.shared as S

            data Todo = { title: S.Title, done: Bool }

            behavior rename : (t: Todo) -> Todo
                constructs Todo

            let rename (t) = Todo { title = t.title, done = t.done }
            """;

    /** A model where a word that is also an imported name is written as something other than a
     *  name: the name of an invariant clause. */
    private static final String LITERAL_MODEL = """
            module example.literal
            import String ( trim )

            data Tag = String
                invariant trim = String.length(value) > 0

            behavior retag : (t: Tag) -> Tag
                constructs Tag

            let retag (t) = Tag(t.value)

            let keep (t: Tag) : String = trim(t.value)
            """;

    /** A model whose behavior is a composition, for what a published one is read back as. */
    private static final String COMPOSING_MODEL = """
            module example.composing

            data Amount = Int
                invariant value >= 0

            data Priced = { of: Amount }

            behavior price : (a: Amount) -> Priced
                constructs Priced

            behavior settle : (p: Priced) -> Amount

            behavior priceAndSettle = price >-> settle

            let price (a) = Priced { of = a }

            let settle (p) = p.of
            """;

    /** A model with a declaration beside the behavior that nothing the behavior crosses reaches. */
    private static final String BESIDE = """
            module example.beside
            import String ( length )

            data Title = String
                invariant length(value) > 0

            data Made = { title: Title }

            data Unrelated = { text: String }

            behavior make : (t: Title) -> Made
                constructs Made

            let make (t) = Made { title = t }
            """;

    /** A model whose behavior names another behavior it takes injected. */
    private static final String DEPENDING = """
            module example.depending
            import String ( length )

            data Amount = Int
                invariant value >= 0

            data Band = String

            behavior bandOf : (a: Amount) -> Band

            behavior charge : (a: Amount) -> Amount
                constructs Amount
                depends on bandOf

            let charge (a, bandOf) = Amount(length(bandOf(a).value))
            """;

    /** A module publishing a value whose name a reader also uses as a field name. */
    private static final String SHADOWING_SHARED = """
            module example.shared exposing ( Title, note )

            data Title = String
                invariant String.length(value) > 0

            let note = "shared"
            """;

    /** It imports that value and never writes it; `note` here is what a field is called. */
    private static final String SHADOWING_MODEL = """
            module example.shadowing
            import example.shared ( Title, note )

            data Todo = { title: Title, note: String }

            behavior rename : (t: Todo) -> Todo
                constructs Todo

            let rename (t) = Todo { title = t.title, note = t.note }
            """;

    /** A module offering a type and a rule written against it, which another module's invariant
     *  reads through. */
    private static final String OFFERING = """
            module example.money exposing ( Amount, atLeast )

            data Amount = Decimal

            let atLeast (a: Amount) : Bool = a.value >= 1.0m
            """;

    private static final String READING = """
            module example.order
            import example.money ( Amount, atLeast )

            data Line = { amount: Amount }
                invariant atLeast(amount)

            behavior price : (l: Line) -> Line
                constructs Line

            let price (l) = Line { amount = l.amount }
            """;

    /** A module reached only by a helper nothing is read through. */
    private static final String FORMATTING = """
            module example.format exposing ( decorate, Style )
            import String ( length )

            data Style = String
                invariant length(value) > 0

            let decorate (s: String) : String = s
            """;

    private static final String USING_FORMAT = """
            module example.model exposing ( Title, describe )
            import String ( length )
            import example.format ( decorate )

            data Title = String
                invariant length(value) > 0

            behavior retitle : (t: Title) -> Title
                constructs Title

            let retitle (t) = Title(t.value)

            let describe (t: Title) : String = decorate(t.value)
            """;

    /** A model with a behavior nothing implements, which is therefore one an implementation may be
     *  supplied for. */
    private static final String INJECTING = """
            module example.injecting

            data Amount = Int

            behavior charge : (a: Amount) -> Amount
                constructs Amount
            """;

    /** A model whose invariant reads a field of what it is given. */
    private static final String READING_A_FIELD = """
            module example.range

            data Range = { min: Int, max: Int }

            data Checked = { range: Range }
                invariant valid(range)

            behavior check : (c: Checked) -> Checked
                constructs Checked

            let check (c) = Checked { range = c.range }

            let valid (r: Range) : Bool = r.min >= 0
            """;

    /** A model whose invariant states a number, for what stating it another way is. */
    private static final String DECIMAL_MODEL = """
            module example.rates

            data Rate = Decimal
                invariant value >= 1.0m

            behavior raise : (r: Rate) -> Rate
                constructs Rate

            let raise (r) = Rate(r.value)
            """;

    /** The same model with a behavior that answers with a union, for what a case being added is. */
    private static final String UNION_MODEL = """
            module example.stale
            import String ( length )

            data Title = String
                invariant length(value) > 0

            data Todo = { title: Title, done: Bool }

            data NotFound = { title: Title }

            data Archived = { title: Title }

            data Outcome = Todo | NotFound

            behavior find : (to: Title) -> Outcome
                constructs Todo

            let find (to) = Todo { title = to, done = false }
            """;

    /**
     * Two builds of one source agree.
     *
     * <p>The compiles are separate, so nothing is shared between what is compared — this is the
     * position an implementation built by an earlier build is in, with the thing that would make it
     * stale not having happened.
     */
    @Test
    void twoBuildsOfOneSourceAgree() {
        Agreement held = DeclarationAgreement.of("example.stale", "rename",
                declarationsOf(MODEL), declarationsOf(MODEL));

        assertInstanceOf(Agreement.Agree.class, held,
                "nothing a crossing depends on differs between them");
    }

    /**
     * An invariant that has been narrowed since the answer was built.
     *
     * <p>What goes wrong without this is quiet: the row states a value the model now admits, the
     * older {@code Title} refuses it, and the run sees a value it built and cannot hand on. That
     * lands where an environment problem lands, and reads as one.
     */
    @Test
    void anInvariantNarrowedSinceTheAnswerWasBuiltIsADisagreement() {
        String narrowed = MODEL.replace("invariant length(value) > 0",
                "invariant length(value) > 3");

        Agreement held = DeclarationAgreement.of("example.stale", "rename",
                declarationsOf(narrowed), declarationsOf(MODEL));

        Agreement.Disagree said = assertInstanceOf(Agreement.Disagree.class, held,
                "an invariant is part of what a value is, so the two read the same value differently");
        assertEquals("example.stale", said.module());
        assertEquals("Title", said.declaration(), "and it says which declaration moved");
    }

    /**
     * A declaration written out differently says the same thing.
     *
     * <p>What a crossing depends on is what a declaration says, and spacing says nothing. A check
     * that reported this would report a stale build every time a file was reformatted, which is the
     * failure this exists to stop being reported for reasons nobody can act on.
     */
    @Test
    void aDeclarationSpacedDifferentlyIsNotADisagreement() {
        String spaced = MODEL
                .replace("data Todo = { title: Title, done: Bool }",
                        "data Todo = {\n    title:   Title,\n    done:    Bool\n}")
                .replace("data Title = String", "// what a todo is called\ndata Title = String");

        Agreement held = DeclarationAgreement.of("example.stale", "rename",
                declarationsOf(spaced), declarationsOf(MODEL));

        assertInstanceOf(Agreement.Agree.class, held,
                "how a declaration is written out is not something a value can be read differently by");
    }

    /**
     * A behavior's body is not part of what a value crossing into it depends on.
     *
     * <p>The body is not published — a reader has the signature and calls it — and an implementation
     * supplied from outside is a body of its own anyway. What the run finds out about a body that has
     * moved is what the rows are there to find out.
     */
    @Test
    void aBodyThatMovedIsNotADisagreement() {
        String rewritten = MODEL.replace("let rename (t, to) = Todo { title = to, done = t.done }",
                "let rename (t, to) = Todo { done = t.done, title = to }");

        Agreement held = DeclarationAgreement.of("example.stale", "rename",
                declarationsOf(rewritten), declarationsOf(MODEL));

        assertInstanceOf(Agreement.Agree.class, held,
                "a `let` body is not read by anything crossing into the answer");
    }

    /**
     * A case added to a union since the answer was built.
     *
     * <p>The quiet one. A row expects the case, the answer has no such case, and what comes back is
     * read at a case the model does not have there — which lands on a comparison, and a comparison is
     * read as a statement about the model.
     */
    @Test
    void aCaseAddedToAUnionSinceTheAnswerWasBuiltIsADisagreement() {
        // Both builds declare `Archived`; only the newer one answers with it. So what differs is the
        // union and nothing else, which is the difference a row expecting that case runs into.
        String answering = UNION_MODEL.replace("data Outcome = Todo | NotFound",
                "data Outcome = Todo | NotFound | Archived");

        Agreement held = DeclarationAgreement.of("example.stale", "find",
                declarationsOf(answering), declarationsOf(UNION_MODEL));

        Agreement.Disagree said = assertInstanceOf(Agreement.Disagree.class, held,
                "the answer has no case for what the row expects");
        assertEquals("Outcome", said.declaration());
    }

    /**
     * A field renamed since the answer was built.
     *
     * <p>The neutral form carries the new name and the older decoder finds nothing under it.
     */
    @Test
    void aFieldRenamedSinceTheAnswerWasBuiltIsADisagreement() {
        String renamed = MODEL.replace("done: Bool", "finished: Bool")
                .replace("done = t.done", "finished = t.finished");

        Agreement held = DeclarationAgreement.of("example.stale", "rename",
                declarationsOf(renamed), declarationsOf(MODEL));

        Agreement.Disagree said = assertInstanceOf(Agreement.Disagree.class, held,
                "a decoder reads fields by name");
        assertEquals("Todo", said.declaration());
    }

    /**
     * A behavior whose signature has moved.
     *
     * <p>What a behavior takes and answers with is the whole of what crosses into it, so an answer
     * built against another signature is being handed values by a shape nothing agreed on.
     */
    @Test
    void aBehaviorSignatureThatMovedIsADisagreement() {
        String moved = MODEL.replace("behavior rename : (t: Todo, to: Title) -> Todo",
                "behavior rename : (t: Todo, to: Title, also: Bool) -> Todo")
                .replace("let rename (t, to) =", "let rename (t, to, also) =");

        Agreement held = DeclarationAgreement.of("example.stale", "rename",
                declarationsOf(moved), declarationsOf(MODEL));

        Agreement.Disagree said = assertInstanceOf(Agreement.Disagree.class, held);
        assertEquals("rename", said.declaration());
    }

    /**
     * A published helper no declaration is read through is not part of a crossing.
     *
     * <p>A module publishes the helpers its invariants call — a reader cannot read what a value is
     * without them — and it publishes what it exposes, because a reader substitutes a value where it
     * is named and expands a helper where it is called. Only the first is read by anything a value
     * crossing into an answer meets: an exposed helper nothing declares its way through is expanded
     * in whatever calls it, and a run's rows never do.
     */
    @Test
    void anExposedHelperNoDeclarationReadsIsNotADisagreement() {
        String moved = EXPOSING_MODEL.replace("let describe (t: Title) : String = trim(t.value)",
                "let describe (t: Title) : String = trim(trim(t.value))");

        Agreement held = DeclarationAgreement.of("example.published", "rename",
                declarationsOf(moved), declarationsOf(EXPOSING_MODEL));

        assertInstanceOf(Agreement.Agree.class, held,
                "nothing a value crossing into the answer meets is read through it");
    }

    /** A helper an invariant does call is part of what the type admits, so it is compared. */
    @Test
    void aHelperAnInvariantCallsIsADisagreementWhenItMoves() {
        String moved = EXPOSING_MODEL.replace("let longEnough (s: String) : Bool = length(s) > 0",
                "let longEnough (s: String) : Bool = length(s) > 3");

        Agreement held = DeclarationAgreement.of("example.published", "rename",
                declarationsOf(moved), declarationsOf(EXPOSING_MODEL));

        assertInstanceOf(Agreement.Disagree.class, held,
                "what a value is admitted by is read through it");
    }

    /**
     * An import list written in another order binds the same names.
     *
     * <p>What an import binds is which names it brings in and under which qualifier. The order they
     * are written in is not something a value can be read differently by.
     */
    @Test
    void anImportListInAnotherOrderIsNotADisagreement() {
        String reordered = ROOT.replace("import example.shared ( Title, Note )",
                "import example.shared ( Note, Title )");

        Agreement held = DeclarationAgreement.of("example.root", "rename",
                declarationsOf(List.of(SHARED, reordered)), declarationsOf(List.of(SHARED, ROOT)));

        assertInstanceOf(Agreement.Agree.class, held,
                "an import list is the names it brings in, not the order they are written in");
    }

    /**
     * An import only a helper nothing is read through needed.
     *
     * <p>The other half of the same rule. A published helper no declaration is read through is not
     * compared, and neither is what it brought in to be written: an import is on the module because
     * something published needed it, and a comparison holding the whole import list would report a
     * build that changed only the thing it just decided not to compare.
     */
    @Test
    void anImportOnlyAnUnreadHelperNeededIsNotADisagreement() {
        String withoutIt = EXPOSING_MODEL
                .replace("import String ( length, trim )", "import String ( length )")
                .replace("let describe (t: Title) : String = trim(t.value)",
                        "let describe (t: Title) : String = t.value");

        Agreement held = DeclarationAgreement.of("example.published", "rename",
                declarationsOf(withoutIt), declarationsOf(EXPOSING_MODEL));

        assertInstanceOf(Agreement.Agree.class, held,
                "what a helper nothing reads through brought in is not read through either");
    }

    /**
     * A number stated with another scale is the same number.
     *
     * <p>What an invariant says is which values it admits, and `1.0m` and `1.00m` admit the same
     * ones — the language says so wherever else two of them meet. A comparison deciding otherwise
     * would report a stale build over a difference the model does not have.
     */
    @Test
    void aDecimalWrittenWithAnotherScaleIsNotADisagreement() {
        String written = DECIMAL_MODEL.replace("value >= 1.0m", "value >= 1.00m");

        Agreement held = DeclarationAgreement.of("example.rates", "raise",
                declarationsOf(written), declarationsOf(DECIMAL_MODEL));

        assertInstanceOf(Agreement.Agree.class, held,
                "the two admit the same values, which is what the invariant says");
    }

    /** And a bound that really moved is still a disagreement. */
    @Test
    void aDecimalBoundThatMovedIsADisagreement() {
        String raised = DECIMAL_MODEL.replace("value >= 1.0m", "value >= 1.5m");

        Agreement held = DeclarationAgreement.of("example.rates", "raise",
                declarationsOf(raised), declarationsOf(DECIMAL_MODEL));

        assertInstanceOf(Agreement.Disagree.class, held);
    }

    /**
     * A module a declaration reaches without importing it is held to as well.
     *
     * <p>A type is reachable qualified whether or not it was imported, so a field may be declared
     * {@code example.shared.Title} with no import line at all. What reads that field's value is that
     * module's declarations either way, and a walk that followed import lines would take the one
     * spelling and not the other — the same narrowed invariant reported for a module that wrote
     * {@code import}, and passed over for one that did not.
     */
    @Test
    void aModuleReachedWithoutAnImportIsHeldToo() {
        String narrowed = SHARED.replace("invariant length(value) > 0",
                "invariant length(value) > 3");

        Agreement held = DeclarationAgreement.of("example.root", "rename",
                declarationsOf(List.of(SHARED, QUALIFYING_ROOT)),
                declarationsOf(List.of(narrowed, QUALIFYING_ROOT)));

        Agreement.Disagree said = assertInstanceOf(Agreement.Disagree.class, held,
                "what the field's type is declared by moved, and nothing imported it");
        assertEquals("example.shared", said.module());
        assertEquals("Title", said.declaration());
    }

    /**
     * A name spelled through an alias and one spelled in full are one name.
     *
     * <p>What a field's type is is which declaration it names, and two builds may reach it by
     * different spellings — the language settles both to the same declaration. A comparison that read
     * the spellings would report a stale build over how a name was written, which is the thing it is
     * written not to do.
     */
    @Test
    void aNameReachedThroughAnAliasIsTheNameItReaches() {
        Agreement held = DeclarationAgreement.of("example.root", "rename",
                declarationsOf(List.of(SHARED, ALIASING_ROOT)),
                declarationsOf(List.of(SHARED, QUALIFYING_ROOT)));

        assertInstanceOf(Agreement.Agree.class, held,
                "both name the same declaration, however each was written");
    }

    /**
     * A word written as something other than a name does not make an import relevant.
     *
     * <p>An import is held to what the compared declarations are written *with*, and what a clause is
     * called is not a name it uses. Reading one as a name makes an import look needed where it is
     * not, and dropping that import then reports a stale build.
     */
    @Test
    void aWordThatIsNotANameDoesNotMakeAnImportRelevant() {
        String withoutIt = LITERAL_MODEL
                .replace("import String ( trim )\n", "")
                .replace("trim(t.value)", "String.trim(t.value)");

        Agreement held = DeclarationAgreement.of("example.literal", "retag",
                declarationsOf(withoutIt), declarationsOf(LITERAL_MODEL));

        assertInstanceOf(Agreement.Agree.class, held,
                "nothing compared here is written with `trim`; a literal saying so is not writing it");
    }

    /**
     * A composition is compared as what it publishes, which is a signature.
     *
     * <p>A module publishes what a composition's stages compute rather than the stages, so what comes
     * back is a signature like any other behavior's. This is what says so: the comparison refuses a
     * composition outright, and a build whose behavior is one goes through here without meeting that
     * refusal. A day when a composition does arrive is a day this fails rather than a day the stages
     * are quietly compared by a rule nobody could read the truth of.
     */
    @Test
    void aCompositionIsComparedAsTheSignatureItPublishes() {
        String moved = COMPOSING_MODEL.replace("data Priced = { of: Amount }",
                "data Priced = { of: Amount, twice: Amount }")
                .replace("let price (a) = Priced { of = a }",
                        "let price (a) = Priced { of = a, twice = a }");

        assertInstanceOf(Agreement.Agree.class,
                DeclarationAgreement.of("example.composing", "priceAndSettle",
                        declarationsOf(COMPOSING_MODEL), declarationsOf(COMPOSING_MODEL)),
                "two builds of one composition agree");
        assertInstanceOf(Agreement.Disagree.class,
                DeclarationAgreement.of("example.composing", "price",
                        declarationsOf(moved), declarationsOf(COMPOSING_MODEL)),
                "and what a stage answers with having moved is a disagreement for that stage");
    }

    /**
     * A helper's parameter renamed, and every use of it with it.
     *
     * <p>What an invariant admits is what its helper computes, and what a parameter is called is not
     * part of that: the two admit the same values. A comparison reading the spelling of a binding
     * would report a stale build for renaming a local, which is a change a crossing cannot see.
     */
    @Test
    void aHelpersParameterRenamedIsNotADisagreement() {
        String renamed = EXPOSING_MODEL
                .replace("let longEnough (s: String) : Bool = length(s) > 0",
                        "let longEnough (text: String) : Bool = length(text) > 0");

        Agreement held = DeclarationAgreement.of("example.published", "rename",
                declarationsOf(renamed), declarationsOf(EXPOSING_MODEL));

        assertInstanceOf(Agreement.Agree.class, held,
                "what a binding is called is not something a value can be read differently by");
    }

    /**
     * A field named the same as something an import brings in.
     *
     * <p>A field's name is what it is called, not a name it reaches something by. Reading it as one
     * would make an import look used where nothing uses it — and then dropping that import, which
     * nothing compared is written with, reports a stale build.
     */
    @Test
    void aFieldNamedLikeAnImportedValueIsNotAReferenceToIt() {
        String withoutIt = SHADOWING_MODEL
                .replace("import example.shared ( Title, note )\n",
                        "import example.shared ( Title )\n");

        Agreement held = DeclarationAgreement.of("example.shadowing", "rename",
                declarationsOf(List.of(SHADOWING_SHARED, withoutIt)),
                declarationsOf(List.of(SHADOWING_SHARED, SHADOWING_MODEL)));

        assertInstanceOf(Agreement.Agree.class, held,
                "the field is called `note`; it does not name what the import brings in");
    }

    /**
     * A helper another module published, which this one's invariant is read through.
     *
     * <p>What a declaration is read through does not have to be its own module's. A rule written in
     * the module that owns the type and called by a reader's invariant is as much a part of what the
     * reader's values are as one written beside it — so a build where that rule tightened admits
     * something else, and a row's value built here is refused there.
     */
    @Test
    void aHelperOfAnotherModuleAnInvariantReadsThroughIsADisagreement() {
        String tightened = OFFERING.replace("a.value >= 1.0m", "a.value >= 5.0m");

        Agreement held = DeclarationAgreement.of("example.order", "price",
                declarationsOf(List.of(tightened, READING)),
                declarationsOf(List.of(OFFERING, READING)));

        Agreement.Disagree said = assertInstanceOf(Agreement.Disagree.class, held,
                "the rule the reader's invariant is read through admits something else now");
        assertEquals("example.money", said.module());
        assertEquals("atLeast", said.declaration());
    }

    /**
     * A helper reading another field of the same value.
     *
     * <p>Which field a rule reads is what the rule says: one that admits every value whose `min` is
     * positive admits a different set from one that admits every value whose `max` is. A comparison
     * that read a field access as the access it is, without which field, would call the two one
     * rule — and hand a row to an answer that refuses a value this model admits.
     */
    @Test
    void aHelperReadingAnotherFieldIsADisagreement() {
        String other = READING_A_FIELD.replace("r.min >= 0", "r.max >= 0");

        Agreement held = DeclarationAgreement.of("example.range", "check",
                declarationsOf(other), declarationsOf(READING_A_FIELD));

        assertInstanceOf(Agreement.Disagree.class, held,
                "the two admit different values, so the declaration reading them moved");
    }

    /**
     * A behavior with the same signature, which one build implements and the other leaves open.
     *
     * <p>Whether a behavior is one an implementation may be supplied for is a fact about the
     * crossing and not about the signature: the two builds disagree about whether anything may be
     * handed in there at all. It does not survive as source, so it travels beside the module.
     */
    @Test
    void aBehaviorLeftOpenInOneBuildAndImplementedInTheOtherIsADisagreement() {
        String implemented = INJECTING + "\nlet charge (a) = Amount(a.value)\n";

        Agreement held = DeclarationAgreement.of("example.injecting", "charge",
                declarationsOf(implemented), declarationsOf(INJECTING));

        assertInstanceOf(Agreement.Disagree.class, held,
                "one of them may have an implementation supplied for it and the other may not");
    }

    /**
     * A module only an unread helper reaches is not held to.
     *
     * <p>It has to be read — a name in that helper is answered against it, and resolution answers
     * every name or none. It is not compared: nothing a value crossing meets is declared there, so
     * a build where it moved, or where it is not there at all, has not moved anything a row depends
     * on. Reading and comparing are two closures and this is where they differ.
     */
    @Test
    void aModuleOnlyAnUnreadHelperReachesIsNotHeldTo() {
        // Its own declaration moved, which is what would be reported if it were held to at all.
        String moved = FORMATTING.replace("invariant length(value) > 0",
                "invariant length(value) > 3");

        Agreement held = DeclarationAgreement.of("example.model", "retitle",
                declarationsOf(List.of(FORMATTING, USING_FORMAT)),
                declarationsOf(List.of(moved, USING_FORMAT)));

        assertInstanceOf(Agreement.Agree.class, held,
                "nothing a declaration is read through is declared there");
    }

    /**
     * A module reached through an import is held to as well.
     *
     * <p>A field of an imported type is read by that module's declarations, so a module whose own
     * declarations agree can still be read by an invariant from a build that has moved. What it
     * reports is the module that differs, which is the imported one and not the one the rows are
     * written for.
     */
    @Test
    void aModuleReachedThroughAnImportIsHeldToo() {
        String narrowed = SHARED.replace("invariant length(value) > 0",
                "invariant length(value) > 3");

        Agreement held = DeclarationAgreement.of("example.root", "rename",
                declarationsOf(List.of(SHARED, ROOT)), declarationsOf(List.of(narrowed, ROOT)));

        Agreement.Disagree said = assertInstanceOf(Agreement.Disagree.class, held,
                "the module the rows are written for agrees, and what it imports does not");
        assertEquals("example.shared", said.module(), "it names the module that moved");
        assertEquals("Title", said.declaration());
    }

    /** Two builds of a model spread over two modules agree, one import deep. */
    @Test
    void twoBuildsOfAModelWithAnImportAgree() {
        Agreement held = DeclarationAgreement.of("example.root", "rename",
                declarationsOf(List.of(SHARED, ROOT)), declarationsOf(List.of(SHARED, ROOT)));

        assertInstanceOf(Agreement.Agree.class, held);
    }

    /**
     * Classes that carry no declarations at all.
     *
     * <p>A jar from before modules carried them, and a name that is not a compiled Souther module,
     * arrive the same way: there is nothing to compare. Answered rather than assumed — the classes
     * may well be of exactly this module, and what is known is that nothing here can say so.
     */
    @Test
    void classesCarryingNoDeclarationsCannotBeToldEitherWay() {
        Agreement held = DeclarationAgreement.of("example.stale", "rename",
                declarationsOf(MODEL), _ -> new PublishedClasses.Carried.NoSuchClass());

        Agreement.Unreadable said = assertInstanceOf(Agreement.Unreadable.class, held,
                "nothing was published, so nothing was established");
        assertInstanceOf(Readback.NotReady.SaysNothing.class, said.reading(),
                "the classes say nothing about it, which is not their saying something unreadable");
        assertEquals("example.stale", said.module());
        assertEquals(Agreement.Side.THE_ANSWER, said.side(),
                "and it is the answer's classes that carry none");
    }

    /**
     * A module that published declarations whose classes are not all there.
     *
     * <p>The module says which classes carry what it declared, and one of them is missing. What was
     * published cannot be read back, so whether it agrees is not something this can say.
     */
    @Test
    void declarationsThatCannotBeReadBackCannotBeToldEitherWay() {
        PublishedClasses incomplete = missing("example.stale.Title",
                declarationsOf(MODEL));

        Agreement held = DeclarationAgreement.of("example.stale", "rename", declarationsOf(MODEL), incomplete);

        Agreement.Unreadable said = assertInstanceOf(Agreement.Unreadable.class, held,
                "a declaration was published and the class carrying it is not there");
        // Which declaration, and not only that something could not be read: the reading found it
        // and the answer carries what it found.
        assertEquals(new Readback.Failure.DeclarationMissing("Title"),
                assertInstanceOf(Readback.NotReady.Unreadable.class, said.reading()).why());
        assertEquals(Agreement.Side.THE_ANSWER, said.side());
    }

    /**
     * A module the answer's classes carry, whose dependency they do not.
     *
     * <p>The plainest way an answer's classes come up short, and the one this said nothing about.
     * Its import line names a module those classes have nothing for, so the module cannot be read —
     * and what a reader had to go on was that what it published cannot be read here, the same
     * sentence an artifact from another compiler gets. There is a module to put on the answer's path
     * and nothing said which.
     */
    @Test
    void aDependencyTheAnswersClassesLeaveOutIsSaidAsThat() {
        PublishedClasses ours = declarationsOf(List.of(SHARED, ROOT));

        Agreement held = DeclarationAgreement.of("example.root", "rename", ours,
                without("example.shared", declarationsOf(List.of(SHARED, ROOT))));

        Agreement.Unreadable said = assertInstanceOf(Agreement.Unreadable.class, held,
                "the module is carried and the module its import line names is not");
        assertEquals(Agreement.Side.THE_ANSWER, said.side());
        assertEquals("example.root", said.module());
        assertEquals(new Readback.Failure.InvalidExposure(
                        new Readback.Exposure.NoSuchModule("example.shared"), List.of()),
                assertInstanceOf(Readback.NotReady.Unreadable.class, said.reading()).why(),
                "and which module is short is what the reader is given");
    }

    /**
     * A declaration the behavior's crossing does not reach is not held to.
     *
     * <p>An answer answers one behavior, and a row of it is handed what that behavior takes and
     * given back what it answers with. A declaration written beside it that nothing crossing meets
     * is not part of that, and holding two builds to it reports a stale build for editing something
     * else in the same file — which is the report this whole check exists to stop being made for
     * reasons nobody can act on.
     *
     * <p>The second half is what keeps the first honest. The same edit made to what the behavior
     * does reach is a disagreement, so the module is being compared and not skipped.
     */
    @Test
    void aDeclarationTheCrossingDoesNotReachIsNotHeldTo() {
        String beside = BESIDE.replace("data Unrelated = { text: String }",
                "data Unrelated = { text: String, more: Int }");
        String reached = BESIDE.replace("data Made = { title: Title }",
                "data Made = { title: Title, more: Int }")
                .replace("let make (t) = Made { title = t }",
                        "let make (t) = Made { title = t, more = 1 }");

        assertInstanceOf(Agreement.Agree.class,
                DeclarationAgreement.of("example.beside", "make",
                        declarationsOf(beside), declarationsOf(BESIDE)),
                "nothing a row of `make` meets is declared by `Unrelated`");
        assertInstanceOf(Agreement.Disagree.class,
                DeclarationAgreement.of("example.beside", "make",
                        declarationsOf(reached), declarationsOf(BESIDE)),
                "and the same edit to what it answers with is one");
    }

    /**
     * A behavior this one takes injected, whose signature has moved.
     *
     * <p>What a row supplies for a dependency crosses into the answer as surely as its inputs do, so
     * the dependency's signature — and the declarations that signature names — are part of what this
     * behavior's crossing depends on. Reached through the {@code depends on} clause, which is what
     * the behavior says about it.
     */
    @Test
    void aDependencyWhoseSignatureMovedIsADisagreement() {
        // What it admits, not what it holds: a body that reads the dependency's answer goes on
        // reading it, so what differs is the declaration and nothing around it.
        String moved = DEPENDING.replace("data Band = String",
                "data Band = String\n    invariant length(value) > 0");

        Agreement held = DeclarationAgreement.of("example.depending", "charge",
                declarationsOf(moved), declarationsOf(DEPENDING));

        Agreement.Disagree said = assertInstanceOf(Agreement.Disagree.class, held,
                "what answers the dependency hands back is read by the row that supplied it");
        assertEquals("Band", said.declaration());
    }

    /**
     * Which build is on which side does not change the answer.
     *
     * <p>This is a question about two sets of declarations and not about one of them. A declaration
     * only one side has is a difference whichever side has it, and a rule the walk applies to ours
     * alone lets whatever their build put there through the guard it was written to meet — a set
     * holding a form, say, which is compared by an equality that reads what this erases. The
     * asymmetry does not show up as a wrong answer on the side that is read; it shows up as no
     * answer at all on the side that is not.
     *
     * <p>Reflexive too. A build held against itself agrees, or nothing else measured here means
     * anything.
     */
    @Test
    void whichSideABuildIsOnDoesNotChangeTheAnswer() {
        String narrowed = MODEL.replace("invariant length(value) > 0",
                "invariant length(value) > 3");
        String withACase = UNION_MODEL.replace("data Outcome = Todo | NotFound",
                "data Outcome = Todo | NotFound | Archived");

        assertEquals(Agreement.Agree.class, kindOf(MODEL, MODEL, "rename"),
                "a build held against itself agrees");
        assertEquals(kindOf(narrowed, MODEL, "rename"), kindOf(MODEL, narrowed, "rename"),
                "an invariant that moved is a disagreement from either side");
        assertEquals(Agreement.Disagree.class, kindOf(narrowed, MODEL, "rename"));
        assertEquals(kindOf(withACase, UNION_MODEL, "find"),
                kindOf(UNION_MODEL, withACase, "find"),
                "and so is a case only one of them has");
        assertEquals(Agreement.Disagree.class, kindOf(withACase, UNION_MODEL, "find"));
    }

    /** What holding {@code ours} against {@code theirs} for {@code behavior} answers with. */
    private static Class<?> kindOf(String ours, String theirs, String behavior) {
        return DeclarationAgreement.of("example.stale", behavior,
                declarationsOf(ours), declarationsOf(theirs)).getClass();
    }

    /** {@code classes} with {@code absent} not on it, as an incomplete jar has it. */
    private static PublishedClasses missing(String absent, PublishedClasses classes) {
        return binaryName -> binaryName.equals(absent)
                ? new PublishedClasses.Carried.NoSuchClass() : classes.of(binaryName);
    }

    /** {@code classes} with nothing of {@code module} on them, as a jar that left a dependency
     *  out has it. */
    private static PublishedClasses without(String module, PublishedClasses classes) {
        return binaryName -> binaryName.equals(module) || binaryName.startsWith(module + ".")
                ? new PublishedClasses.Carried.NoSuchClass() : classes.of(binaryName);
    }

    /** The classes one build of a model spread over several sources emits. */
    private static PublishedClasses declarationsOf(List<String> sources) {
        Compilation compiled = Compilation.ofSources(sources, ModulePath.EMPTY);
        Map<String, byte[]> classes = compiled.db().ask(new Output.All()).value();
        assertEquals(List.of(), diagnosed(compiled), "the model this is measured against compiles");
        return new ClassFileDeclarations(classes::get);
    }

    /**
     * The classes one build of {@code source} emits, read for what they were stamped with.
     *
     * <p>The build is held to compiling. What is being measured is two models that both compile
     * saying different things, and a model that did not compile stamps nothing on its classes — so a
     * broken source would arrive here as "the declarations could not be read", which is a different
     * answer that would look like the one being asked for.
     */
    private static PublishedClasses declarationsOf(String source) {
        Compilation compiled = Compilation.ofSource(source, "Main");
        Map<String, byte[]> classes = compiled.db().ask(new Output.All()).value();
        assertEquals(List.of(), diagnosed(compiled), "the model this is measured against compiles");
        return new ClassFileDeclarations(classes::get);
    }

    /** What a compile refused, as codes — nothing, for every model measured here.
     *
     * <p>Refused, not said: a warning is what a build carries rather than what stops it, and a model
     * measured here may carry one on purpose. An import nothing writes is exactly that, and is what
     * one of these measures. */
    private static List<String> diagnosed(Compilation compiled) {
        return compiled.diagnostics().values().stream().flatMap(List::stream)
                .filter(d -> d.diagnostic().severity() == souther.compiler.diag.Severity.ERROR)
                .map(d -> String.valueOf(d.diagnostic().code())).toList();
    }
}
