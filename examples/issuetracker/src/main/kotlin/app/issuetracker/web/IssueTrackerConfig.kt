// Wires the generated code to Spring. DataSource / DSLContext / TransactionManager and the schema.sql
// run are all left to Boot's autoconfig (spring-boot-starter-jooq + H2); what is added here is the
// generated-side beans.
//
// There are two kinds. An injected behavior gets its implementation (JooqFindIssue and friends). A
// composed behavior gets its dependencies supplied by `bind`, which is the partial application of what
// its `requires` declared — after binding, what is left is the behavior's declared type, so the
// controller only ever passes the business input.
//
// The autoconfig DSLContext goes through a TransactionAwareDataSourceProxy, so the read and the write of
// one attachLabel call use the connection Spring bound to the request's transaction.
package app.issuetracker.web

import app.issuetracker.JooqCreateIssue
import app.issuetracker.JooqFindIssue
import app.issuetracker.JooqStoreLabels

import example.issuetracker.AssigneeOf
import example.issuetracker.AttachLabel
import example.issuetracker.BusyLabels
import example.issuetracker.CountByLabel
import example.issuetracker.CreateIssue
import example.issuetracker.DetachLabel
import example.issuetracker.FindIssue
import example.issuetracker.OpenIssue
import example.issuetracker.SharedLabels
import example.issuetracker.StoreLabels
import example.issuetracker.TopLabels

import org.jooq.DSLContext
import org.jooq.conf.RenderQuotedNames
import org.jooq.conf.Settings

import org.springframework.context.annotation.Bean
import org.springframework.context.annotation.Configuration

@Configuration(proxyBeanMethods = false)
class IssueTrackerConfig {

    /**
     * Turns jOOQ identifier quoting off. JooqAutoConfiguration picks this bean up. Unquoted names are
     * folded to upper case by H2, so the lower-case names in code match the schema's ISSUES /
     * ISSUE_LABELS.
     */
    @Bean
    fun jooqSettings(): Settings = Settings().withRenderQuotedNames(RenderQuotedNames.NEVER)

    // --- the injected outside-world implementations ---
    @Bean
    fun findIssue(dsl: DSLContext): FindIssue = JooqFindIssue(dsl)

    @Bean
    fun createIssue(dsl: DSLContext): CreateIssue = JooqCreateIssue(dsl)

    @Bean
    fun storeLabels(dsl: DSLContext): StoreLabels = JooqStoreLabels(dsl)

    // --- the composed behaviors, with their `requires` bound ---
    @Bean
    fun openIssue(createIssue: CreateIssue): OpenIssue = OpenIssue.bind(createIssue)

    @Bean
    fun attachLabel(findIssue: FindIssue, storeLabels: StoreLabels): AttachLabel =
        AttachLabel.bind(findIssue, storeLabels)

    @Bean
    fun detachLabel(findIssue: FindIssue, storeLabels: StoreLabels): DetachLabel =
        DetachLabel.bind(findIssue, storeLabels)

    // --- the pure behaviors. No requires, so nothing to inject ---
    @Bean
    fun assigneeOf(): AssigneeOf = AssigneeOf.of()

    @Bean
    fun sharedLabels(): SharedLabels = SharedLabels.of()

    @Bean
    fun countByLabel(): CountByLabel = CountByLabel.of()

    @Bean
    fun topLabels(): TopLabels = TopLabels.of()

    @Bean
    fun busyLabels(): BusyLabels = BusyLabels.of()
}
