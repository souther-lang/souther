-- Two seeded issues. i-1 is assigned and carries two labels; i-2 is unassigned and shares one of them,
-- so shared-labels has something to intersect and the label counts have a clear winner (bug: 2, ui: 1).
MERGE INTO issues (id, title, assignee) KEY(id) VALUES ('i-1', 'crash on save', 'kawasima');
MERGE INTO issues (id, title, assignee) KEY(id) VALUES ('i-2', 'typo in the footer', NULL);

MERGE INTO issue_labels (issue_id, label) KEY(issue_id, label) VALUES ('i-1', 'bug');
MERGE INTO issue_labels (issue_id, label) KEY(issue_id, label) VALUES ('i-1', 'ui');
MERGE INTO issue_labels (issue_id, label) KEY(issue_id, label) VALUES ('i-2', 'bug');
