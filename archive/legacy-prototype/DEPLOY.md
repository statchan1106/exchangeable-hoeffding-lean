# Deploying the Blueprint to GitHub Pages

GitHub owner:

```text
statchan1106
```

This project is connected to:

```text
https://github.com/statchan1106/exchangeable-hoeffding-lean
```

## Recommended repository name

A descriptive name would be:

```text
exchangeable-hoeffding-lean
```

With that name, the final Pages URL should be:

```text
https://statchan1106.github.io/exchangeable-hoeffding-lean/
```

## One-time GitHub setup

1. Go to:

```text
https://github.com/new
```

2. Create a repository named:

```text
exchangeable-hoeffding-lean
```

3. Keep it empty: do not add a README, license, or `.gitignore` from the GitHub
   web UI, because this local project already has files.

4. In the repository settings, enable GitHub Pages:

```text
Settings -> Pages -> Source -> GitHub Actions
```

The Lean project lives under:

```text
testlean
```

## After pushing

Open the Actions tab on GitHub and wait for the `Blueprint` workflow.  If it
succeeds, GitHub Pages publishes the committed static site from:

```text
testlean/site
```

The local preview page is:

```text
testlean\site\index.html
```

## If the workflow fails

The `Lean Action CI` workflow is configured to build the Lake package in
`testlean/`.  The `Blueprint` workflow deploys `testlean/site`.

If Python dependency installation fails locally on Windows, use GitHub Actions
instead.  Windows installation can fail because `pygraphviz` requires Microsoft
C++ Build Tools.
