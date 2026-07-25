// The jOOQ implementations of the three injected behaviors. Each extends the generated abstract base
// (which implements Behavior<I, O>), so the class the domain composes with is a Kotlin class here and a
// Java one in ordering — nothing else about the composition changes.
//
// A Kotlin subclass reaches the base's `protected` factories directly, so the unit case IssueNotFound is
// built with the inherited factory. Values that come from the database go through the public derived
// decoder instead, which is what checks the invariants (IssueId / Label / Assignee are all non-empty) on
// data that has been sitting in storage.
//
// SQL exceptions are not caught. A database outage is not a domain outcome, so it is not a case: the
// exception passes through Souther untouched and the boundary maps it to 503 (ADR-0029).
package app.issuetracker

import app.issuetracker.souther.decodeOrFail

import example.issuetracker.CreateIssue
import example.issuetracker.FindIssue
import example.issuetracker.FindIssueResult
import example.issuetracker.Issue
import example.issuetracker.IssueId
import example.issuetracker.StoreLabels

import org.jooq.DSLContext

/** findIssue: the issue and its labels, or the IssueNotFound case when there is no such row. */
class JooqFindIssue(private val dsl: DSLContext) : FindIssue() {
    override fun apply(id: IssueId): FindIssueResult =
        dsl.issueRow(id.value())?.let { Issue.decoder().decodeOrFail(it) } ?: IssueNotFound()
}

/** createIssue: inserts the issue and its labels, and reports it as stored. */
class JooqCreateIssue(private val dsl: DSLContext) : CreateIssue() {
    override fun apply(issue: Issue): Issue {
        dsl.insertIssue(issue)
        dsl.replaceLabels(issue)
        return issue
    }
}

/** storeLabels: writes an existing issue's label set back, and reports it as stored. */
class JooqStoreLabels(private val dsl: DSLContext) : StoreLabels() {
    override fun apply(issue: Issue): Issue {
        dsl.replaceLabels(issue)
        return issue
    }
}
