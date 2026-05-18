# Deploying the Blueprint to GitHub Pages

GitHub owner:

```text
statchan1106
```

This project is not yet connected to a GitHub remote.  To publish the blueprint,
create a new GitHub repository under `statchan1106`, then connect this local
project to it.

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

## Connect this local project

Run these commands from the Git repository root:

```powershell
git remote add origin https://github.com/statchan1106/exchangeable-hoeffding-lean.git
git branch -M main
git add testlean
git add .github/workflows/blueprint.yml
git commit -m "Add exchangeable Hoeffding Lean blueprint"
git push -u origin main
```

This local repository has a parent Git root, and the Lean project lives under:

```text
testlean
```

## After pushing

Open the Actions tab on GitHub and wait for the `Blueprint` workflow.  If it
succeeds, GitHub Pages will publish the blueprint site.

The local preview page is:

```text
testlean\blueprint\web\index.html
```

## If the workflow fails

The most likely first issue is that the Lean files are still in a draft state or
that `leanblueprint checkdecls` needs a compiled Lean project.  The current
workflow only builds the blueprint website and does not run `checkdecls`.

If Python dependency installation fails locally on Windows, use GitHub Actions
instead.  Windows installation can fail because `pygraphviz` requires Microsoft
C++ Build Tools.
