from invoke import task
from pathlib import Path
import shutil
import subprocess


ROOT = Path(__file__).parent
BLUEPRINT = ROOT / "blueprint"


def run(cmd, cwd=ROOT):
    subprocess.run(cmd, cwd=cwd, check=True, shell=True)


@task
def blueprint(c):
    """Build the blueprint web pages with leanblueprint."""
    run("leanblueprint pdf", cwd=BLUEPRINT)
    run("leanblueprint web", cwd=BLUEPRINT)


@task
def clean_blueprint(c):
    """Remove generated blueprint build artifacts."""
    for name in ["print", "web"]:
        path = BLUEPRINT / name
        if path.exists() and path.is_dir():
            shutil.rmtree(path)

