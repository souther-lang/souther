// The one place that knows the issue tables. Both injected write behaviors and the board query below
// go through these extensions, so the SQL shape of an issue is written once.
//
// An issue spans two tables (issues and its issue_labels rows), so reading one produces the Map that
// Issue.decoder() takes: the labels arrive as a list and become a Set on decode, and an absent assignee
// is left out of the Map entirely so the optional field decodes to None (spec: a `?` field is None when
// the key is absent).
package app.issuetracker

import app.issuetracker.souther.orNull

import example.issuetracker.Issue

import org.jooq.DSLContext
import org.jooq.impl.DSL.field
import org.jooq.impl.DSL.name
import org.jooq.impl.DSL.table

// Unquoted identifiers: the Settings bean turns jOOQ's quoting off, and H2 folds unquoted names to
// upper case, so these lower-case names match the schema's ISSUES / ISSUE_LABELS.
internal val ISSUES = table(name("issues"))
internal val ISSUE_LABELS = table(name("issue_labels"))
internal val ID = field(name("id"), String::class.java)
internal val TITLE = field(name("title"), String::class.java)
internal val ASSIGNEE = field(name("assignee"), String::class.java)
internal val ISSUE_ID = field(name("issue_id"), String::class.java)
internal val LABEL = field(name("label"), String::class.java)

/** One issue as Issue.decoder() reads it, or null when there is no such row. */
internal fun DSLContext.issueRow(id: String): Map<String, Any>? =
    select(ID, TITLE, ASSIGNEE).from(ISSUES).where(ID.eq(id)).fetchOne()
        ?.let { issueMap(it[ID], it[TITLE], it[ASSIGNEE], labelsOf(id)) }

/** Every issue, for the board queries. The labels are fetched in one grouped query, not per issue. */
internal fun DSLContext.issueRows(): List<Map<String, Any>> {
    val labels = select(ISSUE_ID, LABEL).from(ISSUE_LABELS).fetchGroups(ISSUE_ID, LABEL)
    return select(ID, TITLE, ASSIGNEE).from(ISSUES).fetch()
        .map { issueMap(it[ID], it[TITLE], it[ASSIGNEE], labels[it[ID]].orEmpty()) }
}

/** Inserts the issue row. The labels are written by replaceLabels. */
internal fun DSLContext.insertIssue(issue: Issue) {
    insertInto(ISSUES)
        .set(ID, issue.id().value())
        .set(TITLE, issue.title())
        .set(ASSIGNEE, issue.assignee().orNull()?.value())
        .execute()
}

/**
 * Replaces an issue's label rows with the set it now carries. Reading the labels out is plain typed
 * access — a generated data's fields have public accessors, and it is construction, not reading, that
 * the generated path guards (spec 8.5).
 */
internal fun DSLContext.replaceLabels(issue: Issue) {
    val id = issue.id().value()
    deleteFrom(ISSUE_LABELS).where(ISSUE_ID.eq(id)).execute()
    issue.labels().forEach { label ->
        insertInto(ISSUE_LABELS).set(ISSUE_ID, id).set(LABEL, label.value()).execute()
    }
}

private fun DSLContext.labelsOf(id: String): List<String> =
    select(LABEL).from(ISSUE_LABELS).where(ISSUE_ID.eq(id)).fetch(LABEL)

private fun issueMap(id: String, title: String, assignee: String?, labels: List<String>): Map<String, Any> =
    buildMap {
        put("id", id)
        put("title", title)
        put("labels", labels)
        assignee?.let { put("assignee", it) }
    }
