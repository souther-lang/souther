package souther.compiler.partition;

import souther.compiler.check.Symbols;
import souther.compiler.check.TypeOps;
import souther.compiler.check.TypeView;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.Requirements;
import souther.compiler.check.ConstructionDescent;
import souther.compiler.inputs.TermPath;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Where a value has to be built under one parameter, and out of what.
 *
 * <p><b>Not the positions of an input.</b> What a behavior declares it takes is
 * {@link souther.compiler.inputs.InputDomain}'s, and what a row has to compose is this. The two are
 * written with the same {@link TermPath} and are about different things: this goes on until there is
 * a value to build, which is further than a report is about. So a path from here is never looked up
 * over there.
 *
 * <p>Where they do meet is how a position is named. A requirement narrowing a position is written
 * into the path here exactly as the reading writes it, so a class fixed at a position under a
 * refinement is a position this builds at under the same name. Written flat, the two would name one
 * location two ways, and a class the caller fixed would be looked for at a path this plan does not
 * have.
 *
 * <p><b>Worked out once and consumed three ways.</b> What each position may take, the search that
 * chooses one position at a time, and the composing of the chosen values back into a record were
 * three recursions over the same declarations, and the third said so — a value came back null "only
 * where the walk that collected the choices and this one disagree". Holding the positions and the
 * shape they compose back into as one value is what makes that disagreement unsayable rather than
 * something a test has to go looking for.
 *
 * <p><b>Made only by {@link #of}, which is where the requirements are put together.</b> A path the
 * caller fixed a value at states what has to hold for that position to exist, and a caller that also
 * hands over requirements of its own is handing over the second half of one fact rather than a
 * second fact (ADR-0114: coverage and construction use one merge, and neither keeps an account of
 * its own). A constructor a caller could reach is that merge being optional, and one caller took the
 * option: a line at {@code query.tag@Tag} was planned against no requirement at all, and the row
 * offered for it put a {@code NoTag} there.
 */
final class ConstructionPlan {

    private final Node root;

    private ConstructionPlan(Node root) {
        this.root = root;
    }

    /** The position the parameter's own value is built at. */
    Node root() {
        return root;
    }

    /** How deep a record is built. Past this a value stops being anything an author recognises as
     *  one input, and a type that refers to itself would not stop at all.
     *
     *  <p>This search's bound and nobody else's. How far the reading of an input goes is settled by
     *  the declarations it opens ({@link souther.compiler.inputs.ExpansionTrace}), which answers a
     *  different question: a value has to be built at a position whether or not a report divides
     *  it. */
    private static final int MAX_DEPTH = 8;

    /**
     * One position of the value being built.
     *
     * <p><b>Where it is, and no more.</b> What is built at a position is a question three of these
     * answer and the fourth does not have: a requirement that settles the value itself leaves
     * nothing to build there, and a type answered for it would be a type nothing is built at. Asked
     * of all four, the one that has no answer has to invent one — the declared type, or the absence
     * dressed as a type — which is the shortfall this vocabulary exists to state going back in under
     * another name. So {@code type()} is each builder's own, and every reader of one already knows
     * which it is holding.
     */
    sealed interface Node permits Slot, Built, Held, Exact {

        /** Where it is. */
        TermPath at();

        /**
         * The newtype names still to put on what this node produces, outermost first.
         *
         * <p>One question of every node and three answers, because what produces the value differs.
         * A record and a collection are composed bare, so every name the position wears is still to
         * go on; a value chosen at a slot arrives already wearing whatever names its own type wears,
         * so what is left is the names the position wore before a requirement narrowed it — and
         * nothing at all where none did.
         *
         * <p>A row at a {@code data SlotN = Slot} carries {@code SlotN(Slot { ... })}, and a
         * {@code data DecisionN = Decision} narrowed to a case that wraps a number carries
         * {@code DecisionN(Special(5))}. A value composed without them is of a type the parameter
         * does not declare.
         */
        List<TypeOps.Layer> worn();
    }

    /**
     * A position the search chooses a value for.
     *
     * @param worn  {@link Node#worn}: the names the position wore before a requirement narrowed
     *              it, since what is chosen here already wears whatever names {@link #type} wears
     * @param fixed whether the caller had already fixed a value here, which is what says a class is
     *              being placed under whatever holds it
     */
    record Slot(TermPath at, Type type, List<TypeOps.Layer> worn, boolean fixed) implements Node {

        Slot {
            worn = List.copyOf(worn);
        }
    }

    /**
     * A sequence composed out of what stands at its element.
     *
     * <p>Only where a class is to be put there. A list nothing is being placed inside is a value
     * like any other and is chosen whole, which is what keeps the rules about how many it holds
     * with the one reader that has them — so this is the shape of a list a row is being built
     * <em>into</em>, and not the shape of every list.
     *
     * <p>One element and not however many. What a class at an element asks for is a list holding a
     * value in it; what the other elements are is a separate question, and answering it here would
     * decide it for every rule at once. A list of one holds an element in the class and nothing
     * else, which is the least a row can be and still meet what was asked.
     *
     * @param worn  {@link Node#worn}: every name the position wears, since what is composed here
     *              is bare
     * @param under the element's own position
     * @param least how many the rules say the list holds at the fewest, which is one where they say
     *              nothing. The element being placed is one of them and the rest are values of the
     *              element's type: a class at an element asks for a list holding a value in it, and
     *              a list that met that and broke the rule about how many it holds is not a row
     */
    record Held(TermPath at, Type type, List<TypeOps.Layer> worn, Node under, int least)
            implements Node {

        Held {
            worn = List.copyOf(worn);
            if (least < 1) {
                throw new IllegalArgumentException(
                        "a list built around an element holds it: " + least);
            }
        }
    }

    /**
     * A position composed out of the ones under it.
     *
     * @param of    what the record is called, which is what the composed value is written as
     * @param worn  {@link Node#worn}: every name the position wears, since what is composed here is
     *              bare. Where a requirement narrowed the position, the names it wore before the
     *              narrowing come first and the narrowed value's own after them — one list, because
     *              putting them back on is one thing done once
     * @param under the positions of its fields, in the order the declaration writes them
     */
    record Built(TermPath at, Type type, TypeSymbol of, List<TypeOps.Layer> worn,
                 Map<String, Node> under) implements Node {

        Built {
            worn = List.copyOf(worn);
            under = java.util.Collections.unmodifiableMap(new LinkedHashMap<>(under));
        }
    }

    /**
     * A position the requirement itself settles the value of.
     *
     * <p>The absence of an optional is the one of these there is. {@code None} is not a narrowed
     * type with something to be chosen inside it — it is a branch that "puts no position anywhere"
     * (ADR-0114) — so there is nothing here for the search to look at and nothing for it to be
     * refused at.
     *
     * <p><b>Beside the value being fixed by the caller and not the same thing.</b> A caller that
     * fixed a value has one to hand over; here nobody handed anything over and the requirement
     * decides, so writing it as a fixed {@link Slot} would mean putting the value into the caller's
     * table as well — a class stating a narrowing and fixing a value at the same position, which is
     * the two accounts ADR-0114 keeps apart.
     *
     * @param exact the value, which is what the requirement came to
     * @param worn  {@link Node#worn}: every name the position wears, since the value arrives bare.
     *              A {@code data MaybeTagN = Tag?} carries {@code MaybeTagN(None)}
     */
    record Exact(TermPath at, FixtureTemplate exact, List<TypeOps.Layer> worn) implements Node {

        Exact {
            if (exact == null) {
                throw new IllegalArgumentException("a position settled at no value is not settled");
            }
            worn = List.copyOf(worn);
        }
    }

    /**
     * A plan, or the position that would have to be two things for there to be one.
     *
     * <p>Two answers because both are ordinary. A caller asking for a class under one case of a sum
     * beside a class under another has asked for a row no value is, which the model settles and this
     * reports; nothing here fell short.
     */
    sealed interface Result {

        /** The plan, which is what a caller that got one goes on with. */
        record Planned(ConstructionPlan plan) implements Result {}

        /** No value is at both, and this is the position and the two it would have to be. */
        record Conflict(TermPath at, Refinement one, Refinement other) implements Result {}
    }

    /**
     * The plan for one parameter, against everything that has to hold of it.
     *
     * <p><b>The requirements are put together here and nowhere else.</b> A path states what has to
     * hold for the position it names to exist ({@link TermPath#requirements}), and a caller may have
     * requirements besides that — a class selects a refinement at its own position, which no path
     * says. Both are read here, so a caller cannot hand over a fixed path under a case and no
     * requirement that the case was taken: the two would be one location decided twice, and the
     * plan would build the position as the sum rather than as the case.
     *
     * @param decided    the paths the caller has already fixed a value at, which are positions this
     *                   search does not choose at and does not look under. Not a depth and not a
     *                   fact about the type: the caller has what goes there, so what the field of a
     *                   record three levels inside it would have offered is nothing this row asks
     * @param additional what has to hold besides whatever {@code decided} already states. Named for
     *                   that, because a caller handing over the whole of it is the arrangement this
     *                   exists to stop
     */
    static Result of(Type declared, TermPath at, Symbols symbols, Set<TermPath> decided,
                     Requirements additional,
                     java.util.function.ToIntBiFunction<TermPath, Type> least) {
        Requirements required = additional;
        for (TermPath fixed : decided) {
            switch (required.merge(fixed.requirements())) {
                case Requirements.Merge.Merged both -> required = both.requirements();
                case Requirements.Merge.Conflict against ->
                        { return new Result.Conflict(against.at(), against.one(), against.other()); }
            }
        }
        // A position said twice. A caller that fixed a value at a position and also requires a
        // narrowing there has stated the narrowing and fixed a value at it, which ADR-0114 keeps
        // apart -- the value stands at the narrowed position and is chosen there, so one location is
        // never decided twice under two names. Nothing a model writes reaches this: the classes that
        // narrow offer no value to fix, and the ones that offer a value narrow nothing. It is the
        // arrangement an optional's classes had before they said which narrowing they were, and it
        // is refused rather than answered by preferring one of the two.
        for (TermPath fixed : decided) {
            if (required.at(fixed) != null) {
                throw new IllegalStateException("`" + fixed + "` is fixed at a value and required to"
                        + " be " + required.at(fixed).spelled() + "; a narrowing states the"
                        + " narrowing and does not also fix a value there, so this is the caller"
                        + " keeping two accounts of one position");
            }
        }
        return new Result.Planned(
                new ConstructionPlan(node(declared, at, symbols, 0, decided, required, least)));
    }

    /** The collections this plan builds out of what stands at their element. */
    List<Held> held() {
        List<Held> out = new ArrayList<>();
        collectHeld(root, out);
        return List.copyOf(out);
    }

    private static void collectHeld(Node node, List<Held> out) {
        switch (node) {
            // Nothing is built under either: one holds a value the search chooses and the other a
            // value the requirement settled, and a collection is neither.
            case Slot _, Exact _ -> { }
            case Built built -> built.under().values().forEach(each -> collectHeld(each, out));
            case Held held -> {
                out.add(held);
                collectHeld(held.under(), out);
            }
        }
    }

    /** Every position a value is chosen at, in the order they are composed. */
    List<Slot> slots() {
        List<Slot> out = new ArrayList<>();
        collect(root, out);
        return List.copyOf(out);
    }

    private static void collect(Node node, List<Slot> out) {
        switch (node) {
            case Slot slot -> out.add(slot);
            case Built built -> built.under().values().forEach(each -> collect(each, out));
            case Held held -> collect(held.under(), out);
            // Not a position a value is chosen at: the requirement settled it, so there is nothing
            // here for the search to offer and nothing for it to be refused at.
            case Exact _ -> { }
        }
    }

    private static Node node(Type declared, TermPath at, Symbols symbols, int depth,
                             Set<TermPath> decided, Requirements required,
                             java.util.function.ToIntBiFunction<TermPath, Type> least) {
        // What the requirements leave standing here, worked out before anything is decided about
        // the position. Read once and in full: what is built, whether the search chooses it, and
        // where every path below it hangs all follow from it.
        Settled settled = settle(declared, at, symbols, required);
        if (settled.exact() != null) {
            refuseWhatWouldStandUnder(settled.at(), decided, required);
            return new Exact(settled.at(), settled.exact(), settled.outer());
        }
        // A position the caller fixed takes the value it was given whatever would have been built
        // there. Asked at the position as the narrowings leave it, which is the name the caller
        // wrote it under: a value fixed under a case is fixed at the case.
        if (decided.contains(settled.at())) {
            return new Slot(settled.at(), settled.building(), settled.outer(), true);
        }
        TermPath here = settled.at();
        Type building = settled.building();
        TypeView view = TypeView.of(building, symbols);
        // The names the position wore before the narrowings, and those with the narrowed type's own
        // after them — which is what a value composed here bare needs. Both are what the position
        // declares, kept: a value written under the narrowed type's names alone is of a type the
        // parameter does not declare.
        List<TypeOps.Layer> worn = settled.outer().isEmpty() ? view.wrappers()
                : outside(settled.outer(), view.wrappers());
        // A sequence with something to be placed inside it. Built out of its element rather than
        // chosen whole, since what is being asked for is a list holding a value in a class and no
        // proposal of a whole list can be asked to hold one.
        if (view.shape() instanceof souther.compiler.check.Shape.Sequence sequence
                && depth < MAX_DEPTH) {
            Node inside = node(sequence.element(), here.element(), symbols, depth + 1, decided,
                    required, least);
            if (holdsAFixedPosition(inside)) {
                return new Held(here, building, worn, inside,
                        Math.max(1, least.applyAsInt(here, building)));
            }
        }
        ConstructionDescent.ProductBuild composed = ConstructionDescent.toBuild(view.shape());
        // A record with no fields composes nothing out of anything, so it is a value to be chosen
        // like any other and not a position made of positions.
        if (depth >= MAX_DEPTH || composed == null || composed.fields().isEmpty()) {
            return new Slot(here, building, settled.outer(), false);
        }
        Map<String, Node> under = new LinkedHashMap<>();
        composed.fields().forEach((field, type) -> under.put(field,
                node(type, here.then(field), symbols, depth + 1, decided, required, least)));
        return new Built(here, building, composed.constructor(), worn, under);
    }

    /**
     * A position with every requirement standing at it applied.
     *
     * <p><b>Every one, because a narrowing takes no level.</b> A refinement does not move to another
     * position (ADR-0114), so a second may stand at the position the first left — an optional
     * holding a sum is narrowed to what it holds and then to the case that turned out to be there,
     * and `query.tag@Some@Tag` is one position with two narrowings at it. Read one at a time, the
     * plan built the sum and the case went missing, which is a value chosen from the wrong type
     * however carefully the first narrowing was applied.
     *
     * @param at       the position as the narrowings leave it, which is the name every path below it
     *                 hangs from and the name a caller that fixed a value here wrote it under
     * @param building what is to be built there, or null where {@code exact} settled it instead
     * @param exact    the value the narrowings settled, or null where they left something to build.
     *                 Exactly one of the two is null: a narrowing either says which values may stand
     *                 here or says which value does
     * @param outer    the names the position wore before the narrowings, which are what a value
     *                 arriving under the narrowed type is still missing
     */
    private record Settled(TermPath at, Type building, FixtureTemplate exact,
                           List<TypeOps.Layer> outer) {

        Settled {
            if ((building == null) == (exact == null)) {
                throw new IllegalArgumentException(
                        "a settled position either has something to build or is a value: "
                                + building + " / " + exact);
            }
            outer = List.copyOf(outer);
        }
    }

    /**
     * {@code declared} at {@code at}, with the requirements standing there applied in turn.
     *
     * <p>A fold and not a walk with a running total beside it. What one narrowing does is two
     * things at once — it changes what stands at the position, and it takes a name off that a value
     * chosen under the narrowed type is then missing — and they are one step. Kept as two locals
     * updated on their own, the second stopped after the first narrowing while the first went on:
     * a case that is a newtype over an optional narrowed to what the optional holds and the case's
     * own name was never put back, so the row carried a value of a type the parameter does not
     * declare. The state is a {@link Settled}, so a step cannot move one half and leave the other.
     */
    private static Settled settle(Type declared, TermPath at, Symbols symbols,
                                  Requirements required) {
        Settled settled = new Settled(at, declared, null, List.of());
        for (Refinement refinement = required.at(settled.at()); refinement != null;
                refinement = required.at(settled.at())) {
            settled = applying(settled, refinement, symbols, required);
            // Nothing narrows what is not there, so a narrowing that settled the value is the end
            // of the chain whatever else was written.
            if (settled.exact() != null) {
                return settled;
            }
        }
        return settled;
    }

    /**
     * One narrowing applied to a settled position: what stands there afterwards, and the name it
     * took off.
     *
     * <p>Both, here, because they are one step. What the position wears now is what a value chosen
     * under the narrowed type will be missing, and it is read from what stands here rather than
     * from the declaration — a narrowing may leave a position wearing a name the next one takes off
     * in turn, and the declaration wore neither.
     */
    private static Settled applying(Settled settled, Refinement refinement, Symbols symbols,
                                    Requirements required) {
        List<TypeOps.Layer> outer = outside(settled.outer(),
                TypeView.of(settled.building(), symbols).wrappers());
        TermPath here = settled.at().refine(refinement);
        if (refinement instanceof Refinement.Presence presence && !presence.present()) {
            // The absence of an optional settles the value rather than narrowing to something to be
            // built: `None` is a branch that puts no position anywhere (ADR-0114). Whether anything
            // was asked for under it is not this reading's question — what stands at a position and
            // what a caller demanded of it are two, and only the caller's side knows both halves of
            // the second.
            return new Settled(here, null, FixtureTemplate.none(), outer);
        }
        return new Settled(here, narrowed(settled.building(), refinement, symbols), null, outer);
    }

    /**
     * That nothing is asked for at or under a position an absence settled.
     *
     * <p>Asked of the whole demand and not of half of it. What a caller asks for is the paths it
     * fixed a value at and the requirements it stated, put together where the plan is made — so a
     * check that read only the requirements would pass a value fixed at {@code x@None.foo}, which a
     * field step adds no requirement for, and drop it in silence.
     *
     * <p>And at the position as well as under it. A refinement does not move to another position,
     * so a second narrowing of one an absence settled is written at that same path: leaving it out
     * as "not below" reads a rule about steps into a value as one about narrowings, which take
     * none. That is what {@link Result.Conflict} is about at a position two narrowings disagree
     * over, and this is the other half of it — the narrowings agree, and there is nothing there for
     * the second to be about.
     *
     * <p>Nothing a model writes reaches either. The absence puts no position anywhere, so nothing
     * derives one to require or to fix. It is refused so that {@link Exact} means what it says: the
     * value is settled here, and there is nothing left below for anything to have asked of.
     */
    private static void refuseWhatWouldStandUnder(TermPath absent, Set<TermPath> decided,
                                                  Requirements required) {
        for (TermPath each : required.refinements().keySet()) {
            if (each.isAtOrUnder(absent)) {
                throw new IllegalStateException("`" + each + "` is required to be "
                        + required.at(each).spelled() + " at or under `" + absent + "`, which holds"
                        + " no value; nothing stands there for a requirement to be about");
            }
        }
        for (TermPath each : decided) {
            if (each.isAtOrUnder(absent)) {
                throw new IllegalStateException("a value is fixed at `" + each + "`, at or under `"
                        + absent + "`, which holds no value; nothing stands there for a value to be"
                        + " written at");
            }
        }
    }

    /** {@code outer} and then {@code inner}, which is the order names are put back on a value. */
    private static List<TypeOps.Layer> outside(List<TypeOps.Layer> outer,
                                               List<TypeOps.Layer> inner) {
        List<TypeOps.Layer> out = new ArrayList<>(outer);
        out.addAll(inner);
        return List.copyOf(out);
    }

    /**
     * Whether anything under {@code inside} is a position the caller fixed a value at.
     *
     * <p>Asked of the plan that was built for it rather than of how the paths are written. Whether
     * one position is under another is a fact about the steps between them, and a rendering runs
     * those together with whatever each is spelled with — so a test on the text has to name every
     * separator a step can wear, and a position one collection further in follows its container with
     * no dot and matched none of them. Built and then read, the only thing compared is one path with
     * itself.
     */
    private static boolean holdsAFixedPosition(Node inside) {
        // A position the caller narrowed is one it asked something of, as much as one it fixed a
        // value at: a class placing a case inside a list is a class placed under the list. Read off
        // the fixed values alone, a list holding a case of a sum was chosen whole and every element
        // of it came back as whatever stands for the element's type.
        if (inside.at().narrowsWhatItReaches()) {
            return true;
        }
        return switch (inside) {
            case Slot slot -> slot.fixed();
            case Built built -> built.under().values().stream()
                    .anyMatch(ConstructionPlan::holdsAFixedPosition);
            case Held held -> holdsAFixedPosition(held.under());
            // A value the requirement settled is as much something asked of the position as one the
            // caller fixed: a list asked to hold a `None` is a list built around it. Reached where
            // the path above it does not narrow, which is a requirement stated at this position
            // rather than at one the path passed through.
            case Exact _ -> true;
        };
    }

    /**
     * The type a value is built at once {@code refinement} has narrowed the position.
     *
     * <p>A narrowing of what stands at the position and not a rereading of the declaration. The
     * position's declared type is still the sum, and the axis still says so — a class of it saying
     * which case a witness takes is not the position becoming that case, and reading the two as one
     * would have a later reader believe the model declares something it does not. What moves is what
     * is being built.
     *
     * <p><b>Only the narrowings that leave something to build reach here.</b> The absence of an
     * optional is not one of them and is answered by {@link #settle}, where the position is settled
     * at a value instead. Answered here, it would have to come back as a type — the declared
     * optional, or what the optional holds — and either is a position built as something the
     * narrowing said is not there. So this returns a type and never null, and a narrowing that
     * settles a value is a case {@link #settle} has to name rather than one this can express.
     */
    private static Type narrowed(Type declared, Refinement refinement, Symbols symbols) {
        return switch (refinement) {
            case Refinement.SumCase one -> Type.ref(one.leaf());
            // What a `Some` leaves at the position is what the optional was declared to hold, which
            // is the same reading the branches under a position are made from
            // (`StructuralInspection.carried`).
            case Refinement.Presence presence -> presence.present() ? held(declared, symbols)
                    : illegal(declared);
        };
    }

    /** The absence reaching the one place that cannot express it, which is this compiler
     *  contradicting itself rather than anything a model can write. */
    private static Type illegal(Type declared) {
        throw new IllegalStateException("`" + Type.show(declared) + "` is asked for the type an"
                + " absence narrows it to; an absence settles the value and narrows no type, so this"
                + " is the plan reading a settled position as one still to be built");
    }

    /**
     * What the optional at this position holds.
     *
     * <p>Asked of the shape rather than of the written type, since the position may wear names: a
     * {@code data MaybeTagN = Tag?} is an optional and holds a {@code Tag}.
     */
    private static Type held(Type declared, Symbols symbols) {
        if (TypeView.of(declared, symbols).shape()
                instanceof souther.compiler.check.Shape.Optional optional) {
            return optional.element();
        }
        // The requirement and the declaration disagreeing about the position's shape, which is this
        // compiler contradicting itself rather than anything a model can write.
        throw new IllegalStateException("`" + Type.show(declared) + "` is asked for what it holds,"
                + " and it is not an optional; the reading of a position and the plan built from it"
                + " disagree about its shape");
    }
}
