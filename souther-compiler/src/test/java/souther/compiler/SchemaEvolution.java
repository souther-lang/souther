package souther.compiler;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.node.ArrayNode;
import tools.jackson.databind.node.ObjectNode;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.IntPredicate;

/**
 * Where a later copy of a schema accepts fewer documents than the copy that shipped.
 *
 * <p>The rule a frozen {@code schemaVersion} is held to (spec, the adequacy report's versioning): the
 * documents it accepts may grow and must not shrink. This is not a decision of that for JSON Schema
 * at large, and refuses to look like one. It lets a schema grow only where growing a part is shown
 * to grow the whole, and asks everything else to be as it shipped, so a change it cannot show to be
 * safe is named as a narrowing and is a decision somebody makes here rather than one that passes
 * unread.
 *
 * <p><b>The ways a part grows.</b> A key taken out of {@code required}, a word added to an
 * {@code enum}, a key added to the {@code properties} of an object that admits no others, and a
 * {@code description} said differently, which changes nothing a document is held to. And a
 * condition on a word of a discriminator that did not ship, wrapped round a branch as it shipped or
 * added to an {@code allOf} with an {@code else} refusing only what was refused already, where the
 * owner, or every branch of it, held the discriminator to an {@code enum} without that word: no
 * document that shipped carries it, so none is asked more of
 * ({@link #withoutConditionsOnWordsThatDidNotShip}).
 *
 * <p><b>Where a part growing grows the whole.</b> Only where the part is asked of a document the way
 * the whole is: under {@code properties}, {@code items}, {@code allOf}, {@code anyOf}, {@code then},
 * {@code else}, an {@code additionalProperties} that is a schema, a {@code contains} with no upper
 * count, and a branch of a {@code oneOf} no other branch can share a document with — which is also
 * what a branch added to a {@code oneOf} has to be, for the same reason. Anywhere else a
 * part accepting more can make the whole accept less: a condition of an {@code if} that holds of more
 * documents sends some of them to a {@code then} that refuses them, a {@code not} refuses whatever
 * its part accepts, two branches of a {@code oneOf} that come to accept one document both refuse it,
 * and a {@code contains} matching more can pass its {@code maxContains}. There a part has to be as it
 * shipped, and so does every definition a {@code $ref} there reaches, since the reference is the
 * same text whatever the definition says.
 */
public final class SchemaEvolution {

    /** Keywords whose value maps a name to something, so the names are not keywords. */
    private static final Set<String> NAMING = Set.of(
            "properties", "$defs", "patternProperties", "dependentSchemas", "dependentRequired");

    private SchemaEvolution() {
    }

    /** Each place {@code current} accepts less than {@code shipped} did, by its path from the root. */
    public static List<String> narrowings(JsonNode shipped, JsonNode current) {
        List<String> out = new ArrayList<>();
        List<Reference> found = new ArrayList<>();
        references(shipped, true, found, "", shipped);
        references(current, true, found, "", current);
        // A reference into no definition reaches a part this cannot say stays as it shipped, so
        // whatever is changed there is a narrowing as far as this can tell.
        for (Reference each : found) {
            if (each.definition() == null) {
                out.add(each.written() + ": a reference this does not follow");
            }
        }
        Set<String> asShipped = definitionsReachedWhereNothingMayGrow(found);
        Roots roots = new Roots(shipped, current);
        compare(shipped, current, "", true, out, roots);
        JsonNode shippedDefinitions = shipped.path("$defs");
        JsonNode currentDefinitions = current.path("$defs");
        for (String name : shippedDefinitions.propertyNames()) {
            String at = "/$defs/" + name;
            if (!currentDefinitions.has(name)) {
                out.add(at + ": no longer here");
            } else {
                compare(shippedDefinitions.get(name), currentDefinitions.get(name), at,
                        !asShipped.contains(name), out, roots);
            }
        }
        return out;
    }

    /**
     * Compares one schema with its later copy.
     *
     * @param mayGrow whether a part here accepting more makes the whole accept more; where it does
     *                not, the two have to be alike apart from what they say about themselves
     * @param roots   the two whole schemas, which a {@code $ref} in either is followed into
     */
    private static void compare(JsonNode shipped, JsonNode current, String at, boolean mayGrow,
                                List<String> out, Roots roots) {
        if (!shipped.isObject() || !current.isObject()) {
            if (!alike(shipped, current)) {
                out.add(at + ": " + shipped + " shipped and " + current + " now");
            }
            return;
        }
        if (!mayGrow) {
            if (!alike(shipped, current)) {
                out.add(at + ": changed where a part accepting more can make the whole accept less");
            }
            return;
        }
        compareGrowing(shipped, withoutConditionsOnWordsThatDidNotShip(shipped, current, roots),
                at, out, roots);
    }

    /** The same, of a part that may grow: each key as it shipped, and any added since. */
    private static void compareGrowing(JsonNode shipped, JsonNode current, String at,
                                       List<String> out, Roots roots) {
        for (String key : shipped.propertyNames()) {
            if (key.equals("description") || key.equals("$defs")) {
                continue;
            }
            String here = at + "/" + key;
            if (!current.has(key)) {
                out.add(here + ": no longer here");
                continue;
            }
            JsonNode was = shipped.get(key);
            JsonNode is = current.get(key);
            switch (key) {
                case "required" -> {
                    Set<String> added = words(is);
                    added.removeAll(words(was));
                    if (!added.isEmpty()) {
                        out.add(here + ": now requires " + added);
                    }
                }
                case "enum" -> {
                    Set<String> gone = words(was);
                    gone.removeAll(words(is));
                    if (!gone.isEmpty()) {
                        out.add(here + ": no longer allows " + gone);
                    }
                }
                case "properties" -> {
                    for (String name : was.propertyNames()) {
                        if (!is.has(name)) {
                            out.add(here + "/" + name + ": no longer here");
                        } else {
                            compare(was.get(name), is.get(name), here + "/" + name, true, out,
                                    roots);
                        }
                    }
                    // A key added where the object admits no others was refused before and is
                    // held to its own schema now. Where it admits others, the key was held to
                    // what they are held to, and its own schema can be narrower.
                    if (!(closed(shipped) && closed(current))) {
                        for (String name : is.propertyNames()) {
                            if (!was.has(name)) {
                                out.add(here + "/" + name + ": added to an object that admits"
                                        + " other keys");
                            }
                        }
                    }
                }
                case "items", "then", "else" -> compare(was, is, here, true, out, roots);
                case "additionalProperties" ->
                        compare(was, is, here, was.isObject(), out, roots);
                case "contains" -> compare(was, is, here,
                        !shipped.has("maxContains") && !current.has("maxContains"), out, roots);
                // Every branch has to take a document, so one added is one more thing asked of it.
                case "allOf" -> eachBranch(was, is, here, out, _ -> true, _ -> false, roots);
                // Some branch has to take it, so one added takes more and refuses nothing a
                // shipped branch took — here, where what is here accepting more is the whole
                // accepting more, which is the only place this is reached.
                case "anyOf" -> eachBranch(was, is, here, out, _ -> true, _ -> true, roots);
                case "oneOf" -> eachBranch(was, is, here, out,
                        i -> exclusive(was, i, shipped, roots.shipped())
                                && exclusive(is, i, current, roots.current()),
                        i -> exclusive(is, i, current, roots.current()), roots);
                default -> compare(was, is, here, false, out, roots);
            }
        }
        for (String key : current.propertyNames()) {
            if (!shipped.has(key) && !key.equals("description")) {
                out.add(at + "/" + key + ": not in what shipped");
            }
        }
    }

    /**
     * {@code current} without the conditions it adds on a word its discriminator did not ship
     * with, which narrow nothing that shipped.
     *
     * <p>A document is held to such a condition only where its discriminator is the new word, and
     * the owner of the {@code allOf} held that discriminator to an {@code enum} without it: every
     * document carrying the word was refused before, so what is asked of one is asked of no
     * document that shipped. A condition on a word the enum had, or on a discriminator the owner
     * held to no {@code enum}, is not taken out and is compared as any other part is.
     *
     * <p>Where the condition wraps what shipped: the branch it stands in, taken out, is the branch
     * that shipped. Or where it is a branch of the {@code allOf} added after the ones that shipped,
     * the {@code allOf} itself among them: such a branch asks only its {@code else} of a document
     * that shipped, and that narrows nothing where it is absent or refuses only keys the owner as
     * it shipped refused already ({@link #asksNothingOfWhatShipped}).
     *
     * <p>The words a discriminator shipped with are those of the owner's own {@code enum}, or —
     * where the owner names it in none of its own properties — those of the branches of its
     * {@code oneOf} or {@code anyOf}, where each of them holds the discriminator to an
     * {@code enum} or refuses an object holding it: a document carrying another word was refused
     * by every branch.
     */
    private static JsonNode withoutConditionsOnWordsThatDidNotShip(JsonNode shipped,
                                                                   JsonNode current,
                                                                   Roots roots) {
        JsonNode was = shipped.path("allOf");
        JsonNode is = current.path("allOf");
        boolean noneShipped = !shipped.has("allOf");
        if (!is.isArray() || (!noneShipped && (!was.isArray() || is.size() < was.size()))) {
            return current;
        }
        Set<String> asked = new LinkedHashSet<>();
        for (JsonNode each : is) {
            JsonNode held = followed(each, roots.current(), new HashSet<>());
            if (held != null) {
                asked.addAll(held.path("if").path("properties").propertyNames());
            }
        }
        Map<String, Set<String>> shippedWords = wordsShipped(shipped, roots.shipped(), asked);
        if (shippedWords.isEmpty()) {
            return current;
        }
        ObjectNode copy = (ObjectNode) current.deepCopy();
        ArrayNode branches = (ArrayNode) copy.get("allOf");
        int asShipped = noneShipped ? 0 : was.size();
        for (int i = 0; i < asShipped; i++) {
            branches.set(i, withoutAWrapper(was.get(i), is.get(i), shippedWords));
        }
        for (int i = branches.size() - 1; i >= asShipped; i--) {
            if (asksNothingOfWhatShipped(branches.get(i), shipped, shippedWords, roots)) {
                branches.remove(i);
            }
        }
        if (noneShipped && branches.isEmpty()) {
            copy.remove("allOf");
        }
        return copy;
    }

    /**
     * Each discriminator of {@code shipped} and the words it shipped with
     * ({@link #withoutConditionsOnWordsThatDidNotShip}). A key no branch names, that a condition
     * now {@code asked} about, shipped with none where every branch refuses an object holding it.
     */
    private static Map<String, Set<String>> wordsShipped(JsonNode shipped, JsonNode root,
                                                         Set<String> asked) {
        Map<String, Set<String>> out = new HashMap<>();
        for (String name : shipped.path("properties").propertyNames()) {
            JsonNode held = shipped.get("properties").get(name).path("enum");
            if (held.isArray()) {
                out.put(name, words(held));
            }
        }
        for (String keyword : List.of("oneOf", "anyOf")) {
            List<JsonNode> branches = new ArrayList<>();
            for (JsonNode each : shipped.path(keyword)) {
                JsonNode branch = followed(each, root, new HashSet<>());
                if (branch == null) {
                    return out;
                }
                branches.add(branch);
            }
            if (branches.isEmpty()) {
                continue;
            }
            Set<String> named = new LinkedHashSet<>(asked);
            branches.forEach(branch -> named.addAll(branch.path("properties").propertyNames()));
            for (String name : named) {
                if (shipped.path("properties").has(name)) {
                    continue;
                }
                Set<String> words = new LinkedHashSet<>();
                boolean everyBranchSays = true;
                for (JsonNode branch : branches) {
                    JsonNode held = branch.path("properties").path(name).path("enum");
                    if (held.isArray()) {
                        words.addAll(words(held));
                    } else if (!refusesAnObjectHolding(branch, name, root, new HashSet<>())) {
                        everyBranchSays = false;
                    }
                }
                if (everyBranchSays) {
                    out.put(name, words);
                }
            }
        }
        return out;
    }

    /**
     * Whether {@code branch}, added to an {@code allOf}, asks no document that shipped anything:
     * it is a conditional and nothing beside, on a word its discriminator did not ship with, so a
     * document that shipped takes its {@code else} — and that is absent, or refuses only an object
     * holding keys {@code shipped} refused every object holding.
     */
    private static boolean asksNothingOfWhatShipped(JsonNode branch, JsonNode shipped,
                                                    Map<String, Set<String>> shippedWords,
                                                    Roots roots) {
        JsonNode held = followed(branch, roots.current(), new HashSet<>());
        if (held == null || !held.has("if") || !onlyAConditional(held)
                || !onANewWord(held.get("if"), shippedWords)) {
            return false;
        }
        if (!held.has("else")) {
            return true;
        }
        JsonNode otherwise = held.get("else");
        for (String key : otherwise.propertyNames()) {
            if (!Set.of("not", "description").contains(key)) {
                return false;
            }
        }
        JsonNode refused = otherwise.path("not");
        for (String key : refused.propertyNames()) {
            if (!key.equals("required")) {
                return false;
            }
        }
        Set<String> keys = words(refused.path("required"));
        if (keys.isEmpty()) {
            return false;
        }
        for (String key : keys) {
            if (!refusesAnObjectHolding(shipped, key, roots.shipped(), new HashSet<>())) {
                return false;
            }
        }
        return true;
    }

    /** The branch {@code now}, with what wraps {@code before} on a new word taken out. */
    private static JsonNode withoutAWrapper(JsonNode before, JsonNode now,
                                            Map<String, Set<String>> shippedWords) {
        if (!before.isObject() || !now.isObject()) {
            return now;
        }
        if (!before.has("if") && now.has("if") && now.has("else") && onlyAConditional(now)
                && onANewWord(now.get("if"), shippedWords)) {
            return withoutAWrapper(before, now.get("else"), shippedWords);
        }
        if (before.has("if") && now.has("if")) {
            ObjectNode copy = (ObjectNode) now.deepCopy();
            for (String key : List.of("then", "else")) {
                if (before.has(key) && now.has(key)) {
                    copy.set(key, withoutAWrapper(before.get(key), now.get(key), shippedWords));
                }
            }
            return copy;
        }
        return now;
    }

    /**
     * Whether {@code wrapper} holds a document to the conditional and to nothing beside it: a key
     * of any other kind, such as a {@code required} or a {@code not}, asks every document more,
     * whatever its discriminator is.
     */
    private static boolean onlyAConditional(JsonNode wrapper) {
        for (String key : wrapper.propertyNames()) {
            if (!Set.of("if", "then", "else", "description").contains(key)) {
                return false;
            }
        }
        return true;
    }

    /**
     * Whether {@code condition} asks of a document that its discriminator is one word, which the
     * enum that held the discriminator when it shipped did not have.
     */
    private static boolean onANewWord(JsonNode condition, Map<String, Set<String>> shippedWords) {
        JsonNode named = condition.path("properties");
        if (!named.isObject() || named.size() != 1) {
            return false;
        }
        String discriminator = named.propertyNames().iterator().next();
        JsonNode word = named.get(discriminator).path("const");
        return word.isString() && shippedWords.containsKey(discriminator)
                && !shippedWords.get(discriminator).contains(word.asString())
                && words(condition.path("required")).contains(discriminator);
    }

    /**
     * The branches as shipped, each compared with the one at its place now, and any added after
     * them.
     *
     * <p>A branch added after the ones that shipped narrows nothing where {@code mayBeAdded} says
     * no other branch can share a document with it: a document that shipped matching one branch
     * matches that one still and never the new one, and a document only the new one takes was
     * refused before. A branch taken out, or added where it could share one, is a narrowing.
     */
    private static void eachBranch(JsonNode was, JsonNode is, String at, List<String> out,
                                   IntPredicate mayGrow, IntPredicate mayBeAdded, Roots roots) {
        if (is.size() < was.size()) {
            out.add(at + ": " + was.size() + " branches shipped and " + is.size() + " now");
            return;
        }
        for (int i = was.size(); i < is.size(); i++) {
            if (!mayBeAdded.test(i)) {
                out.add(at + "/" + i + ": added where another branch can take what it takes");
            }
        }
        for (int i = 0; i < was.size(); i++) {
            compare(was.get(i), is.get(i), at + "/" + i, mayGrow.test(i), out, roots);
        }
    }

    /** The schema that shipped and its later copy, each whole. */
    private record Roots(JsonNode shipped, JsonNode current) {}

    /**
     * Whether no other branch of {@code branches} accepts a document branch {@code at} does.
     *
     * <p>Shown one of two ways. By a key the document must carry to match the branch, held there to
     * one value no other branch allows: every other branch holds the same key to a different
     * {@code const}. Or by a key the document must carry that no other branch lets an object carry
     * at all, where the branch takes objects alone ({@link #refusesAnObjectHolding}). Either way a
     * document the branch comes to accept is refused by every other branch, and the {@code oneOf}
     * still matches exactly one.
     *
     * @param owner the object the {@code oneOf} is a keyword of, whose {@code required} the branch is
     *              asked under as well
     * @param root  the schema the {@code oneOf} is in, which a {@code $ref} is followed into
     */
    private static boolean exclusive(JsonNode branches, int at, JsonNode owner, JsonNode root) {
        return toldApartByAConst(branches, at, owner)
                || toldApartByAKeyNoOtherAdmits(branches, at, owner, root);
    }

    /**
     * Whether branch {@code at} takes objects alone, and requires a key that every other branch
     * refuses an object to hold.
     */
    private static boolean toldApartByAKeyNoOtherAdmits(JsonNode branches, int at, JsonNode owner,
                                                        JsonNode root) {
        JsonNode branch = followed(branches.get(at), root, new HashSet<>());
        if (branch == null || !"object".equals(branch.path("type").asString(""))) {
            return false;
        }
        Set<String> required = words(branch.path("required"));
        required.addAll(words(owner.path("required")));
        for (String key : required) {
            boolean onlyHere = true;
            for (int other = 0; other < branches.size(); other++) {
                if (other != at
                        && !refusesAnObjectHolding(branches.get(other), key, root, new HashSet<>())) {
                    onlyHere = false;
                }
            }
            if (onlyHere) {
                return true;
            }
        }
        return false;
    }

    /**
     * Whether {@code schema} refuses every object holding {@code key}: it takes no objects, or it
     * admits no keys but the ones it names and does not name this one, or something it asks of
     * every document does — each branch of a {@code oneOf} or an {@code anyOf} it holds, or some
     * part of an {@code allOf}.
     *
     * <p>False wherever that is not shown, which keeps the branch beside it from growing: a
     * reference into part of a definition, or one met again on the way, is not followed.
     *
     * @param followed the definitions already followed on the way here
     */
    private static boolean refusesAnObjectHolding(JsonNode schema, String key, JsonNode root,
                                                  Set<String> followed) {
        JsonNode held = followed(schema, root, followed);
        if (held == null) {
            return false;
        }
        if (held.has("type") && held.get("type").isString()
                && !held.get("type").asString().equals("object")) {
            return true;
        }
        if (closed(held) && !held.path("properties").has(key) && !held.has("patternProperties")) {
            return true;
        }
        for (String keyword : List.of("oneOf", "anyOf")) {
            if (held.has(keyword)) {
                boolean every = true;
                for (JsonNode each : held.get(keyword)) {
                    every &= refusesAnObjectHolding(each, key, root, new HashSet<>(followed));
                }
                if (every) {
                    return true;
                }
            }
        }
        for (JsonNode each : held.path("allOf")) {
            if (refusesAnObjectHolding(each, key, root, new HashSet<>(followed))) {
                return true;
            }
        }
        return false;
    }

    /**
     * {@code schema}, or the whole definition its {@code $ref} names — or null where the reference
     * points into part of one, or at one already in {@code followed}.
     */
    private static JsonNode followed(JsonNode schema, JsonNode root, Set<String> followed) {
        if (!schema.has("$ref")) {
            return schema;
        }
        String written = schema.get("$ref").asString();
        String definition = SchemaReference.definition(written);
        if (definition == null || !written.equals("#/$defs/" + definition)
                || !followed.add(definition) || !root.path("$defs").has(definition)) {
            return null;
        }
        return followed(root.get("$defs").get(definition), root, followed);
    }

    private static boolean toldApartByAConst(JsonNode branches, int at, JsonNode owner) {
        JsonNode branch = branches.get(at);
        Set<String> required = words(branch.path("required"));
        required.addAll(words(owner.path("required")));
        for (String key : branch.path("properties").propertyNames()) {
            JsonNode held = branch.get("properties").get(key);
            if (!held.has("const") || !required.contains(key)) {
                continue;
            }
            boolean onlyHere = true;
            for (int other = 0; other < branches.size(); other++) {
                JsonNode there = branches.get(other).path("properties").path(key);
                if (other != at && !(there.has("const") && !there.get("const").equals(held.get("const")))) {
                    onlyHere = false;
                }
            }
            if (onlyHere) {
                return true;
            }
        }
        return false;
    }

    /**
     * Every definition some {@code $ref} reaches from a place nothing may grow, directly or through
     * another such definition.
     *
     * <p>The whole definition a reference points into, where it points at a part inside one: what
     * this keeps as it shipped is a definition, and keeping a part of one would need this to say
     * which other parts the part depends on.
     */
    private static Set<String> definitionsReachedWhereNothingMayGrow(List<Reference> found) {
        Set<String> out = new HashSet<>();
        for (Reference each : found) {
            if (!each.mayGrow() && each.definition() != null) {
                out.add(each.definition());
            }
        }
        boolean grew = true;
        while (grew) {
            grew = false;
            for (Reference each : found) {
                if (each.from() != null && each.definition() != null && out.contains(each.from())
                        && out.add(each.definition())) {
                    grew = true;
                }
            }
        }
        return out;
    }

    /**
     * One {@code $ref}: as written, the definition it points into or null where it points into
     * none, whether it stands where a part may grow, and the definition it is written inside or
     * null for one outside every definition.
     */
    private record Reference(String written, String definition, boolean mayGrow, String from) {}

    /**
     * Every {@code $ref} in {@code node}, with whether it stands where a part may grow.
     *
     * @param root the whole schema {@code node} is in, which a {@code $ref} is followed into
     */
    private static void references(JsonNode node, boolean mayGrow, List<Reference> out,
                                   String from, JsonNode root) {
        if (node.isArray()) {
            node.forEach(each -> references(each, mayGrow, out, from, root));
            return;
        }
        if (!node.isObject()) {
            return;
        }
        if (node.has("$ref")) {
            String written = node.get("$ref").asString();
            out.add(new Reference(written, SchemaReference.definition(written), mayGrow,
                    from.isEmpty() ? null : from));
        }
        for (String key : node.propertyNames()) {
            JsonNode value = node.get(key);
            switch (key) {
                case "description", "$ref" -> {
                }
                case "$defs" -> {
                    for (String name : value.propertyNames()) {
                        references(value.get(name), true, out, name, root);
                    }
                }
                case "properties" -> {
                    for (String name : value.propertyNames()) {
                        references(value.get(name), mayGrow, out, from, root);
                    }
                }
                case "items", "then", "else", "allOf", "anyOf" ->
                        references(value, mayGrow, out, from, root);
                case "additionalProperties" -> references(value, mayGrow, out, from, root);
                case "contains" -> references(value, mayGrow && !node.has("maxContains"), out,
                        from, root);
                case "oneOf" -> {
                    for (int i = 0; i < value.size(); i++) {
                        references(value.get(i), mayGrow && exclusive(value, i, node, root), out,
                                from, root);
                    }
                }
                default -> references(value, false, out, from, root);
            }
        }
    }

    /** Whether an object admits no keys but the ones it names. */
    private static boolean closed(JsonNode schema) {
        return schema.has("additionalProperties")
                && schema.get("additionalProperties").isBoolean()
                && !schema.get("additionalProperties").asBoolean();
    }

    /**
     * Whether two parts of a schema hold a document to the same things: equal, apart from what
     * either says about itself in a {@code description}.
     *
     * <p>A {@code description} is a keyword only where a keyword stands. Under a keyword that maps
     * names to schemas the same word is the name of a key a document carries, and is compared.
     */
    private static boolean alike(JsonNode a, JsonNode b) {
        return alike(a, b, false);
    }

    private static boolean alike(JsonNode a, JsonNode b, boolean names) {
        if (a.isObject() && b.isObject()) {
            Set<String> keys = new LinkedHashSet<>();
            a.propertyNames().forEach(keys::add);
            b.propertyNames().forEach(keys::add);
            for (String key : keys) {
                if (!names && key.equals("description")) {
                    continue;
                }
                if (!a.has(key) || !b.has(key)
                        || !alike(a.get(key), b.get(key), !names && NAMING.contains(key))) {
                    return false;
                }
            }
            return true;
        }
        if (a.isArray() && b.isArray()) {
            if (a.size() != b.size()) {
                return false;
            }
            for (int i = 0; i < a.size(); i++) {
                if (!alike(a.get(i), b.get(i), false)) {
                    return false;
                }
            }
            return true;
        }
        return a.equals(b);
    }

    private static Set<String> words(JsonNode array) {
        Set<String> out = new LinkedHashSet<>();
        array.forEach(each -> out.add(each.asString()));
        return out;
    }
}
