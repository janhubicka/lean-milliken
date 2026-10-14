# Publishing this documentation to the GitHub Wiki tab

The maintained source of the researcher wiki is `docs/wiki/` in the
`lean-milliken` repository. Its front page is `docs/wiki/README.md`.

The GitHub Wiki tab is **a different Git repository** from the source tree,
so merely committing files under `docs/wiki/` does not make those pages
appear at `https://github.com/janhubicka/lean-milliken/wiki`.

## One-time initialization (required by GitHub)

GitHub doesn't create the separate `.wiki.git` repository until someone
creates the first Wiki page through the website. Do this once:

1. Open **https://github.com/janhubicka/lean-milliken/wiki** and choose
   **Create the first page** (make sure you are signed into a repository
   account with Wiki edit permission).
2. Set the page title to **Home** and enter a temporary sentence, e.g.,
   “This page is populated automatically from docs/wiki.”
3. Click **Save Page**. This initializes the Wiki Git repository.

After saving the first **Home** page, GitHub's `gollum` event
triggers the publishing workflow automatically. This should populate all
pages from `docs/wiki/` without a second manual action. If it does not,
open **https://github.com/janhubicka/lean-milliken/actions/workflows/publish-wiki.yml**,
choose **Run workflow**, select **main**, and run it.

The automation is already installed as
[`.github/workflows/publish-wiki.yml`](../../.github/workflows/publish-wiki.yml).
It also runs automatically whenever the wiki source or its publishing
workflow changes on the default branch.

## Content and link handling

The workflow uses
[`Andrew-Chen-Wang/github-wiki-action@v5`](https://github.com/Andrew-Chen-Wang/github-wiki-action)
with `path: docs/wiki` and preprocessing enabled. Consequently:

- `docs/wiki/README.md` becomes the Wiki's **Home.md**.
- Other Markdown source filenames become Wiki pages.
- Links between local wiki pages are rewritten as Wiki page links.
- Links to source files *outside* `docs/wiki/` are rewritten to
  version-pinned repository URLs, so the published wiki does not acquire
  broken relative links.
- Publishing updates the Wiki's Git history with ordinary commits.
  **It never force-pushes the Wiki**.

The source-controlled files, not manual edits to the GitHub Wiki tab, are
authoritative. Future audit updates should be made in `docs/wiki/` and
reviewed through the usual pull requests. A direct edit to the GitHub
Wiki tab risks being overwritten at the next synchronization.

## Troubleshooting

If the workflow says that the `owner/repository.wiki.git` repository does
not exist or cannot be cloned, verify that the initial **Home** page was
created and saved through the Wiki UI. If the repository exists but
publishing is denied, check the workflow's `contents: write` permission and
the repository's GitHub Actions policies.

For the immediately readable documentation, independent of whether the
GitHub Wiki has been initialized, use the
[version-controlled wiki home](README.md).

## Verification record

The source pages were initially merged as audit PR #145 (14 October 2026).
The publishing workflow was committed later as a separate change. **Do not
report the GitHub Wiki tab as published until its workflow run has succeeded
and the Home page can actually be opened there.**
