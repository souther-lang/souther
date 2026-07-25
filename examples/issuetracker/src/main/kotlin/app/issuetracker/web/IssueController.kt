// The REST boundary. Every route is the same three steps: decode the outside values into domain values,
// call one behavior, fold its output union into a status and a body.
//
// Two things are worth looking at.
//
// A request body arrives as a plain Map and is handed to the *derived* decoder — there is no Kotlin data
// class mirroring the request shape. The shape is already declared in issues.sou, and the derived decoder
// is what checks the invariants (a Label is non-empty, and so on) and reports failures as Raoh issues with
// their JSON paths. A data class here would duplicate the domain shape and would reject a malformed body
// in Jackson, before the decoder that has the actual rules ever ran.
//
// A behavior's output is a generated `sealed` union, so `when` over it is exhaustive and the Kotlin
// compiler rejects a missing case by name. This is what account's `case-of` macro had to hand-build for
// Clojure: Souther's `match` totality carried across the boundary, here for free.
package app.issuetracker.web

import app.issuetracker.souther.decodeOrFail
import app.issuetracker.souther.invoke

import example.issuetracker.Assigned
import example.issuetracker.AssigneeOf
import example.issuetracker.AssigneeOfResult
import example.issuetracker.AttachLabel
import example.issuetracker.AttachLabelResult
import example.issuetracker.Board
import example.issuetracker.CountByLabel
import example.issuetracker.DetachLabel
import example.issuetracker.DetachLabelResult
import example.issuetracker.FindIssue
import example.issuetracker.FindIssueResult
import example.issuetracker.Issue
import example.issuetracker.IssueId
import example.issuetracker.IssueNotFound
import example.issuetracker.LabelCounts
import example.issuetracker.LabelRanking
import example.issuetracker.LabelRequest
import example.issuetracker.LabelSet
import example.issuetracker.NewIssue
import example.issuetracker.NoLabels
import example.issuetracker.OpenIssue
import example.issuetracker.OpenIssueResult
import example.issuetracker.SharedLabels
import example.issuetracker.TopLabels
import example.issuetracker.Unassigned

import org.springframework.http.HttpStatus
import org.springframework.http.ResponseEntity
import org.springframework.transaction.annotation.Transactional
import org.springframework.web.bind.annotation.DeleteMapping
import org.springframework.web.bind.annotation.GetMapping
import org.springframework.web.bind.annotation.PathVariable
import org.springframework.web.bind.annotation.PostMapping
import org.springframework.web.bind.annotation.RequestBody
import org.springframework.web.bind.annotation.RequestParam
import org.springframework.web.bind.annotation.RestController

@RestController
class IssueController(
    private val openIssue: OpenIssue,
    private val findIssue: FindIssue,
    private val attachLabel: AttachLabel,
    private val detachLabel: DetachLabel,
    private val assigneeOf: AssigneeOf,
    private val sharedLabels: SharedLabels,
    private val countByLabel: CountByLabel,
    private val topLabels: TopLabels,
    private val boardQuery: BoardQuery,
) {

    /**
     * Opens an issue from a raw comma-separated label string. openIssue normalizes it, and reports
     * NoLabels when nothing survives — which is a domain outcome, so it is a case rather than an
     * exception, and it lands here as a returned value. Two rows are written (the issue and its labels),
     * hence the transaction.
     */
    @PostMapping("/issues")
    @Transactional
    fun open(@RequestBody body: Map<String, Any>): ResponseEntity<Any> =
        openIssue(NewIssue.decoder().decodeOrFail(body)).toResponse()

    @GetMapping("/issues/{id}")
    fun find(@PathVariable id: String): ResponseEntity<Any> =
        findIssue(issueId(id)).toResponse()

    /** The optional assignee, opened by the domain: Some(Assignee(name)) is 200, None is 204. */
    @GetMapping("/issues/{id}/assignee")
    fun assignee(@PathVariable id: String): ResponseEntity<Any> =
        when (val found = findIssue(issueId(id))) {
            is Issue -> assigneeOf(found).toResponse()
            is IssueNotFound -> notFound()
        }

    /**
     * Adds a label. attachLabel reads the issue, inserts into its label Set and writes it back, so the
     * read and the write belong in one transaction — otherwise a concurrent call could drop a label by
     * writing back a set it read before the other one landed.
     */
    @PostMapping("/issues/{id}/labels")
    @Transactional
    fun attach(@PathVariable id: String, @RequestBody body: Map<String, Any>): ResponseEntity<Any> =
        attachLabel(labelRequest(body + ("id" to id))).toResponse()

    @DeleteMapping("/issues/{id}/labels/{label}")
    @Transactional
    fun detach(@PathVariable id: String, @PathVariable label: String): ResponseEntity<Any> =
        detachLabel(labelRequest(mapOf("id" to id, "label" to label))).toResponse()

    /**
     * Set intersection over two issues. Either one missing is a 404. The union is narrowed to a Kotlin
     * nullable by an exhaustive fold (issueOrNull) rather than by a type test, so the two lookups read as
     * `?: return` and the totality is still the compiler's to check.
     */
    @GetMapping("/issues/{a}/shared-labels/{b}")
    fun shared(@PathVariable a: String, @PathVariable b: String): ResponseEntity<Any> {
        val left = findIssue(issueId(a)).issueOrNull() ?: return notFound()
        val right = findIssue(issueId(b)).issueOrNull() ?: return notFound()
        return ResponseEntity.ok(LabelSet.encoder().encode(sharedLabels(left, right)))
    }

    /** How many issues carry each label, as a Map<String, Int> the encoder hands over as a JSON object. */
    @GetMapping("/labels/counts")
    fun counts(): Map<String, Any> =
        LabelCounts.encoder().encode(countByLabel(boardQuery.board()))

    @GetMapping("/labels/top")
    fun top(@RequestParam(defaultValue = "3") n: Long): Map<String, Any> =
        LabelRanking.encoder().encode(topLabels(boardQuery.board(), n))

    private fun issueId(id: String): IssueId = IssueId.decoder().decodeOrFail(id)

    private fun labelRequest(raw: Map<String, Any>): LabelRequest =
        LabelRequest.decoder().decodeOrFail(raw)
}

// --- folding the output unions ---
// One `when` per union. The unions are distinct types (each behavior seals its own), so each gets its own
// fold, and each is checked for exhaustiveness on its own.

private fun OpenIssueResult.toResponse(): ResponseEntity<Any> = when (this) {
    is Issue -> ResponseEntity.status(HttpStatus.CREATED).body(Issue.encoder().encode(this))
    is NoLabels -> ResponseEntity.badRequest().body(mapOf("error" to "no_labels"))
}

private fun FindIssueResult.toResponse(): ResponseEntity<Any> = when (this) {
    is Issue -> ok(this)
    is IssueNotFound -> notFound()
}

private fun FindIssueResult.issueOrNull(): Issue? = when (this) {
    is Issue -> this
    is IssueNotFound -> null
}

private fun AttachLabelResult.toResponse(): ResponseEntity<Any> = when (this) {
    is Issue -> ok(this)
    is IssueNotFound -> notFound()
}

private fun DetachLabelResult.toResponse(): ResponseEntity<Any> = when (this) {
    is Issue -> ok(this)
    is IssueNotFound -> notFound()
}

private fun AssigneeOfResult.toResponse(): ResponseEntity<Any> = when (this) {
    is Assigned -> ResponseEntity.ok(Assigned.encoder().encode(this))
    is Unassigned -> ResponseEntity.noContent().build()
}

private fun ok(issue: Issue): ResponseEntity<Any> = ResponseEntity.ok(Issue.encoder().encode(issue))

private fun notFound(): ResponseEntity<Any> = ResponseEntity.notFound().build()

// A behavior of two arguments is not Behavior<I, O> — that contract is unary — so these two get their own
// operator, and every behavior call at this boundary reads as a function call.
private operator fun SharedLabels.invoke(a: Issue, b: Issue): LabelSet = apply(a, b)

private operator fun TopLabels.invoke(board: Board, n: Long): LabelRanking = apply(board, n)
