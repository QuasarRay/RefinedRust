# RefinedRust — automated GitLab mirror

This is an **unofficial, read-only mirror** of the original [RefinedRust development repository](https://gitlab.mpi-sws.org/lgaeher/refinedrust-dev).

## Source code

- **[Browse upstream main](https://github.com/QuasarRay/RefinedRust/tree/upstream/main)**
- **[Browse upstream branches](https://github.com/QuasarRay/RefinedRust/branches)**
- **[Browse upstream tags](https://github.com/QuasarRay/RefinedRust/tags)**

All upstream branches are synchronized into the `upstream/` branch namespace (for example, GitLab `main` becomes GitHub `upstream/main`). GitLab tags retain their original names. Branch and tag history is preserved; changes to mirrored refs (including upstream force-pushes and deletions) are replicated.

The GitHub default branch, `main`, contains only this mirror's documentation and GitHub Actions automation. Keeping it separate prevents upstream changes from deleting the synchronization workflow and avoids executing upstream-provided CI code on the default branch.

## Synchronization

The [mirror workflow](.github/workflows/sync-upstream.yml) fetches from:

```text
https://gitlab.mpi-sws.org/lgaeher/refinedrust-dev.git
```

It runs automatically every six hours, on changes to the workflow, and can be started manually using **Actions → Sync RefinedRust from GitLab → Run workflow**.

No access token is needed to read the public upstream; the workflow uses GitHub's built-in `GITHUB_TOKEN` with repository contents write permission to update its mirror refs.

**Upstream project:** https://gitlab.mpi-sws.org/lgaeher/refinedrust-dev  
**Original authors and license:** See the upstream repository.
