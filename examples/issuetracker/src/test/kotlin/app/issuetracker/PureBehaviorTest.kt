// The generated types used without a framework: decode outside values, run a pure behavior, read the
// result back through the encoder. What is checked here is the codec path around Set and Map, which the
// `.sou` `example` blocks cannot reach — a fixture there is written in Souther notation, whereas these go
// through the JSON-shaped decoder the boundary actually uses (a JSON array becomes a Set, a Map is
// encoded as a JSON object).
package app.issuetracker

import app.issuetracker.souther.decodeOrFail

import example.issuetracker.Assigned
import example.issuetracker.AssigneeOf
import example.issuetracker.Board
import example.issuetracker.CountByLabel
import example.issuetracker.GroupByAssignee
import example.issuetracker.Issue
import example.issuetracker.LabelCounts
import example.issuetracker.LabelSet
import example.issuetracker.SharedLabels
import example.issuetracker.Unassigned
import example.issuetracker.Workload

import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertInstanceOf
import org.junit.jupiter.api.Test

class PureBehaviorTest {

    @Test
    fun `a JSON array of labels decodes into a deduplicated Set`() {
        val issue = issue("i-1", "crash on save", listOf("bug", "ui", "bug"))

        assertEquals(setOf("bug", "ui"), issue.labels().map { it.value() }.toSet())
        assertEquals(2, issue.labels().size, "the repeated label collapsed on decode")
    }

    @Test
    fun `countByLabel counts each label across the board`() {
        val board = board(
            issueMap("i-1", "crash on save", listOf("bug", "ui")),
            issueMap("i-2", "typo", listOf("bug")),
        )

        val counts = LabelCounts.encoder().encode(CountByLabel.of().apply(board))["counts"]

        assertEquals(mapOf("bug" to 2L, "ui" to 1L), counts, "a Map output encodes to a JSON object")
    }

    @Test
    fun `groupByAssignee buckets the issue ids under each assignee`() {
        val board = board(
            issueMap("i-1", "crash on save", listOf("bug"), assignee = "kawasima"),
            issueMap("i-2", "typo", listOf("ui"), assignee = "aoyagi"),
            issueMap("i-3", "npe", listOf("bug"), assignee = "kawasima"),
            issueMap("i-4", "nobody looks at this", listOf("bug")),
        )

        val byAssignee = Workload.encoder().encode(GroupByAssignee.of().apply(board))["byAssignee"]

        assertEquals(
            mapOf("kawasima" to listOf("i-1", "i-3"), "aoyagi" to listOf("i-2")),
            byAssignee,
            "a list under a map value encodes as a JSON array, each id bare; the unassigned issue is absent",
        )
    }

    @Test
    fun `sharedLabels is the intersection of the two label sets`() {
        val shared = SharedLabels.of().apply(
            issue("i-1", "a", listOf("bug", "ui")),
            issue("i-2", "b", listOf("ui", "docs")),
        )

        assertEquals(listOf("ui"), LabelSet.encoder().encode(shared)["labels"])
    }

    @Test
    fun `assigneeOf opens Some and takes the None arm when unassigned`() {
        val assigned = assertInstanceOf(
            Assigned::class.java,
            AssigneeOf.of().apply(issue("i-1", "a", listOf("bug"), assignee = "kawasima")),
        )
        assertEquals(mapOf("name" to "kawasima"), Assigned.encoder().encode(assigned))

        assertInstanceOf(
            Unassigned::class.java,
            AssigneeOf.of().apply(issue("i-2", "b", listOf("bug"))),
            "no assignee takes the None arm",
        )
    }

    private fun issue(id: String, title: String, labels: List<String>, assignee: String? = null): Issue =
        Issue.decoder().decodeOrFail(issueMap(id, title, labels, assignee))

    private fun board(vararg issues: Map<String, Any>): Board =
        Board.decoder().decodeOrFail(mapOf("issues" to issues.toList()))

    // An absent assignee key decodes to None — the same shape the jOOQ read produces for a NULL column.
    private fun issueMap(
        id: String,
        title: String,
        labels: List<String>,
        assignee: String? = null,
    ): Map<String, Any> =
        buildMap {
            put("id", id)
            put("title", title)
            put("labels", labels)
            assignee?.let { put("assignee", it) }
        }
}
