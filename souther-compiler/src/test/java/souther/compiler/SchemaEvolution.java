package souther.compiler;

import tools.jackson.databind.JsonNode;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
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
 * {@code description} said differently, which changes nothing a document is held to.
 *
 * <p><b>Where a part growing grows the whole.</b> Only where the part is asked of a document the way
 * the whole is: under {@code properties}, {@code items}, {@code allOf}, {@code anyOf}, {@code then},
 * {@code else}, an {@code additionalProperties} that is a schema, a {@code contains} with no upper
 * count, and a branch of a {@code oneOf} no other branch can share a document with. Anywhere else a
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
        references(shipped, true, found, "");
        references(current, true, found, "");
        // A reference into no definition reaches a part this cannot say stays as it shipped, so
        // whatever is changed there is a narrowing as far as this can tell.
        for (Reference each : found) {
            if (each.definition() == null) {
                out.add(each.written() + ": a reference this does not follow");
            }
        }
        Set<String> asShipped = definitionsReachedWhereNothingMayGrow(found);
        compare(shipped, current, "", true, out);
        JsonNode shippedDefinitions = shipped.path("$defs");
        JsonNode currentDefinitions = current.path("$defs");
        for (String name : shippedDefinitions.propertyNames()) {
            String at = "/$defs/" + name;
            if (!currentDefinitions.has(name)) {
                out.add(at + ": no longer here");
            } else {
                compare(shippedDefinitions.get(name), currentDefinitions.get(name), at,
                        !asShipped.contains(name), out);
            }
        }
        return out;
    }

    /**
     * Compares one schema with its later copy.
     *
     * @param mayGrow whether a part here accepting more makes the whole accept more; where it does
     *                not, the two have to be alike apart from what they say about themselves
     */
    private static void compare(JsonNode shipped, JsonNode current, String at, boolean mayGrow,
                                List<String> out) {
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
                            compare(was.get(name), is.get(name), here + "/" + name, true, out);
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
                case "items", "then", "else" -> compare(was, is, here, true, out);
                case "additionalProperties" -> compare(was, is, here, was.isObject(), out);
                case "contains" -> compare(was, is, here,
                        !shipped.has("maxContains") && !current.has("maxContains"), out);
                case "allOf", "anyOf" -> eachBranch(was, is, here, out, _ -> true);
                case "oneOf" -> eachBranch(was, is, here, out,
                        i -> exclusive(was, i, shipped) && exclusive(is, i, current));
                default -> compare(was, is, here, false, out);
            }
        }
        for (String key : current.propertyNames()) {
            if (!shipped.has(key) && !key.equals("description")) {
                out.add(at + "/" + key + ": not in what shipped");
            }
        }
    }

    private static void eachBranch(JsonNode was, JsonNode is, String at, List<String> out,
                                   IntPredicate mayGrow) {
        if (was.size() != is.size()) {
            out.add(at + ": " + was.size() + " branches shipped and " + is.size() + " now");
            return;
        }
        for (int i = 0; i < was.size(); i++) {
            compare(was.get(i), is.get(i), at + "/" + i, mayGrow.test(i), out);
        }
    }

    /**
     * Whether no other branch of {@code branches} accepts a document branch {@code at} does.
     *
     * <p>Shown by a key the document must carry to match the branch, held there to one value no
     * other branch allows: every other branch holds the same key to a different {@code const}. So a
     * document the branch comes to accept carries that value and is refused by every other branch,
     * and the {@code oneOf} still matches exactly one.
     *
     * @param owner the object the {@code oneOf} is a keyword of, whose {@code required} the branch is
     *              asked under as well
     */
    private static boolean exclusive(JsonNode branches, int at, JsonNode owner) {
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

    private static void references(JsonNode node, boolean mayGrow, List<Reference> out,
                                   String from) {
        if (node.isArray()) {
            node.forEach(each -> references(each, mayGrow, out, from));
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
                        references(value.get(name), true, out, name);
                    }
                }
                case "properties" -> {
                    for (String name : value.propertyNames()) {
                        references(value.get(name), mayGrow, out, from);
                    }
                }
                case "items", "then", "else", "allOf", "anyOf" ->
                        references(value, mayGrow, out, from);
                case "additionalProperties" -> references(value, mayGrow, out, from);
                case "contains" ->
                        references(value, mayGrow && !node.has("maxContains"), out, from);
                case "oneOf" -> {
                    for (int i = 0; i < value.size(); i++) {
                        references(value.get(i), mayGrow && exclusive(value, i, node), out, from);
                    }
                }
                default -> references(value, false, out, from);
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
