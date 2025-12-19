#!/usr/bin/env python3
"""
Submit Sobolev-Q3 lemmas to Aristotle.

Usage:
    python submit_aristotle.py                # Submit all input files
    python submit_aristotle.py 01_sobolev_embedding.md  # Submit specific file
"""

import asyncio
import sys
import os
from pathlib import Path

# Ensure API key is set
if "ARISTOTLE_API_KEY" not in os.environ:
    print("❌ Set ARISTOTLE_API_KEY first:")
    print('   export ARISTOTLE_API_KEY="your_key"')
    sys.exit(1)

from aristotlelib import Project, set_api_key

set_api_key(os.environ["ARISTOTLE_API_KEY"])

INPUT_DIR = Path(__file__).parent / "blueprint" / "aristotle_input"


async def submit_file(filepath: Path):
    """Submit a single file to Aristotle."""
    print(f"📤 Submitting: {filepath.name}")

    try:
        project = await Project.prove_from_file(
            input_file_path=str(filepath),
            auto_add_imports=False,
            validate_lean_project=False,
        )
        print(f"   ✅ Submitted! Project ID: {project.project_id}")
        print(f"   📊 Status: {project.status}")
        return project.project_id
    except Exception as e:
        print(f"   ❌ Error: {e}")
        return None


async def submit_all():
    """Submit all input files."""
    print("🚀 Submitting Sobolev-Q3 lemmas to Aristotle")
    print("=" * 60)

    input_files = sorted(INPUT_DIR.glob("*.md"))

    if not input_files:
        print(f"❌ No .md files found in {INPUT_DIR}")
        return

    print(f"📁 Found {len(input_files)} input files\n")

    project_ids = []
    for f in input_files:
        pid = await submit_file(f)
        if pid:
            project_ids.append((f.name, pid))
        print()

    print("=" * 60)
    print("📋 Summary:")
    for name, pid in project_ids:
        print(f"   {name}: {pid}")

    print(f"\n✅ Submitted {len(project_ids)} projects")
    print("\n💡 Check status with:")
    print("   uv run python check_aristotle.py")


async def submit_one(filename: str):
    """Submit a specific file."""
    filepath = INPUT_DIR / filename
    if not filepath.exists():
        print(f"❌ File not found: {filepath}")
        return

    await submit_file(filepath)


async def main():
    if len(sys.argv) < 2:
        await submit_all()
    else:
        await submit_one(sys.argv[1])


if __name__ == "__main__":
    asyncio.run(main())
