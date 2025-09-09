#!/usr/bin/env python3
# -*- coding: utf-8 -*-
#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
"""
ivy_llm.py

Usage:
  ivy_llm path/to/model.ivy \
      --model gpt-5 \
      --dry-run   # optional, shows what would be appended without modifying file

Requirements:
  pip install openai
Environment:
  export OPENAI_API_KEY=sk-...
"""

import os
import re
import sys
import json
import shlex
import argparse
import subprocess
from datetime import datetime
from pathlib import Path

try:
    from openai import OpenAI
except ImportError:
    print("Please `pip install openai` first.", file=sys.stderr)
    sys.exit(1)

# --- Customize this to your liking ---
FIXED_PROMPT = (
    "You are an expert on distributed protocols and the Ivy language. "
    "Given an Ivy protocol module below, produce exactly ONE fenced code "
    "block tagged `ivy` that contains ONLY Ivy invariant declarations needed "
    "to prove the target property (no prose, no comments). Use capital letters "
    "for all quantified variables. All other names should start with lower-case letters. Do not include anything outside the code block. "
    "Try to avoid quantifier alternations in the invariants. " 
    "Do not add module headers; just invariant declarations suitable for pasting. "
)

# A tight regex that captures the FIRST fenced ivy block in the response.
FENCE_RE = re.compile(
    r"```(?:\s*ivy[^\n]*)\n(?P<body>[\s\S]*?)```",
    re.IGNORECASE
)

EXPL_RE = re.compile(
    r"=== BEGIN EXPLANATION ===(?P<body>[\s\S]*?)=== END EXPLANATION ===",
    re.IGNORECASE
)


def extract_expl(text: str) -> str:
    """
    Return the contents of the first explanation block.
    If not found, try a conservative fallback that collects lines starting with 'invariant'.
    """
    m = EXPL_RE.search(text)
    if m:
        body = m.group("body").strip()
        return body

    return None

def extract_ivy_block(text: str) -> str:
    """
    Return the contents of the first ```ivy ... ``` code fence.
    If not found, try a conservative fallback that collects lines starting with 'invariant'.
    """
    m = FENCE_RE.search(text)
    if m:
        body = m.group("body").strip()
        # Ensure it contains at least one 'invariant'
        if re.search(r'(^|\n)\s*invariant\b', body):
            return body

    # Fallback: collect invariant lines until a blank gap (very conservative)
    lines = []
    found = False
    for line in text.splitlines():
        if re.match(r'^\s*invariant\b', line):
            found = True
            lines.append(line.rstrip())
        elif found:
            # Stop when we hit an empty line after finding invariants
            if not line.strip():
                break
            lines.append(line.rstrip())
    candidate = "\n".join(lines).strip()
    if candidate:
        return candidate

    raise ValueError("No Ivy code fence or invariant lines found in model output.")

context = None

def call_openai(client: OpenAI, model: str, fixed_prompt: str, ivy_source: str, temperature: float = 0.2, effort = "medium") -> str:
    """
    Use OpenAI Responses API to generate Ivy invariants.
    """
    global context
    api_key = os.environ.get("OPENAI_API_KEY")
    if not api_key:
        raise RuntimeError("OPENAI_API_KEY is not set in the environment.")


    print ('=== BEGIN PROMPT ===')
    print (fixed_prompt)
    print ('=== END PROMPT ===')

    # Compose single input string: fixed instructions + the Ivy source payload.
    # Using Responses API with `instructions` + `input` (see official SDK examples).
    # https://github.com/openai/openai-python  |  https://platform.openai.com/docs/api-reference/responses
    payload = f"{fixed_prompt}\n\n"

    if ivy_source is not None:
        payload += (
            "=== BEGIN IVY MODEL ===\n"
            f"{ivy_source}\n"
            "=== END IVY MODEL ===\n"
        )

    payload += "\nReturn only a single fenced code block tagged `ivy` containing invariants. Use only capital letters for quantified variables."

    print ("[GPT5] Thinking...")
    resp = client.responses.create(
        model=model,                 # e.g., "gpt-5"
        instructions="You are a precise, terse Ivy assistant.",
        input=payload,
        previous_response_id = context,
        reasoning={"effort": effort}, # "minimal", "low", "medium", or "high"
        # temperature=temperature,
    )

    # `output_text` flattens the response content into a string per the SDK.
    # https://github.com/openai/openai-python
    context=resp.id
    text = resp.output_text

    # print ('=== BEGIN FULL GPT OUTPUT ===') 
    # print (text)
    # print ('=== END FULL GPT OUTPUT ===') 

    if not text or not text.strip():
        raise RuntimeError("Empty response from model.")
    return text

def run_ivy_check(ivy_path: Path) -> tuple[int, str, str]:
    """
    Run ivy_check on the given file. Returns the process's return code.
    """
    cmd = f"ivy_check {shlex.quote(str(ivy_path))}"
    print(f"\n[ivy_check] Running: {cmd}")
    try:
        proc = subprocess.run(
            cmd, shell=True, check=False, capture_output=True, text=True
        )
        # print(proc.stdout)
        if proc.stderr:
            print(proc.stderr, file=sys.stderr)
        return proc.returncode, proc.stdout, proc.stderr
    except FileNotFoundError:
        print("Error: `ivy_check` not found on PATH.", file=sys.stderr)
        return 127

def append_block(ivy_path: Path, ivy_text: str, block_text: str, dry_run: bool = False) -> None:
    """
    Append the extracted Ivy block to the file, wrapped with clear sentinels.
    """
    stamped = (
        "\n\n" +
        f"### --- BEGIN GENERATED INVARIANTS ({datetime.utcnow().isoformat()}Z) ---\n"
        "\n" +
        block_text.strip() +
        "\n\n" +
        "### --- END GENERATED INVARIANTS ---\n"
    )
    if dry_run:
        print("\n[DRY RUN] Would append the following to the Ivy file:\n")
        print(stamped)
        return

    boiler = (
        "proof [this] {\n"
        "    tactic expl\n"
        "}\n"
    )


    with ivy_path.open("w", encoding="utf-8") as f:
        f.write(ivy_text)
        f.write(stamped)
        f.write(boiler)

def main():
    p = argparse.ArgumentParser(description="Generate Ivy invariants with LLM's.")
    p.add_argument("ivy_file", type=Path, help="Path to the Ivy source file")
    p.add_argument("--model", default="gpt-5", help="OpenAI model (default: gpt-5)")
    p.add_argument("--temperature", type=float, default=0.2, help="Sampling temperature (default: 0.2)")
    p.add_argument("--dry-run", action="store_true", help="Show what would be appended without modifying the file")
    p.add_argument("--no-check", action="store_true", help="Skip running ivy_check after appending")
    p.add_argument("--fixed-prompt", default=FIXED_PROMPT, help="Override the fixed prompt text")
    p.add_argument("--block", type=Path, default=None, help="Read the LLM answer from a file")
    p.add_argument("--iters", type=int, default=5, help="maximum number of iterations")
    p.add_argument(
        "--effort",
        default="medium",
        choices=("minimal", "low", "medium", "high"),
        help="Reasoning effort",
    )
    args = p.parse_args()
    iters = 0

    print (args.block)
    
    ivy_path = args.ivy_file
    if not ivy_path.exists():
        print(f"Error: {ivy_path} does not exist.", file=sys.stderr)
        sys.exit(2)

    ivy_text = ivy_path.read_text(encoding="utf-8")

    if args.block is None:
        # Call OpenAI (GPT-5) to get invariant code block
        try:
            client = OpenAI()  # picks up OPENAI_API_KEY from env
        except Exception as e:
            print(f"OpenAI call failed: {e}", file=sys.stderr)
            sys.exit(3)

    fixed_prompt=args.fixed_prompt
    ivy_source = ivy_text
    
    for iter in range(args.iters):
        if args.block is None:
        # Call OpenAI (GPT-5) to get invariant code block
            try:
                raw = call_openai(
                    client,
                    model=args.model,
                    fixed_prompt=fixed_prompt,
                    ivy_source=ivy_source,
                    temperature=args.temperature,
                    effort=args.effort
                )
            except Exception as e:
                print(f"OpenAI call failed: {e}", file=sys.stderr)
                sys.exit(3)

            # Extract a fenced ```ivy block
            try:
                ivy_block = extract_ivy_block(raw)
            except Exception as e:
                print(f"Failed to extract Ivy code block: {e}", file=sys.stderr)
                # Helpful for debugging: dump the model output to a sidecar file
                dump_path = ivy_path.with_suffix(ivy_path.suffix + ".model_output.txt")
                dump_path.write_text(raw, encoding="utf-8")
                print(f"Model output saved to: {dump_path}", file=sys.stderr)
                sys.exit(4)

        else:

            if not args.block.exists():
                print(f"Error: {args.block} does not exist.", file=sys.stderr)
                sys.exit(2)

            ivy_block =  args.block.read_text(encoding="utf-8")

        print ('=== BEGIN GPT GUESS ===')
        print (ivy_block)
        print ('=== END GPT GUESS ===')

        # Append block to the Ivy file (or show in dry-run)
        ivy_path = Path("temp.ivy")
        append_block(ivy_path, ivy_text, ivy_block, dry_run=args.dry_run)

        # Run ivy_check unless skipped or dry-run
        if not args.no_check and not args.dry_run:
            rc,stdout,stderr = run_ivy_check(ivy_path)
            if rc == 0:
                print("[ivy_check] ✔ Success")
                exit(0)
            else:
                print(f"[ivy_check] ✖ Failed with exit code {rc}", file=sys.stderr)
                expl = extract_expl(stdout)
                if args.block is not None:
                    exit(0)
                if expl is not None:
                    # print (f'expl: {expl}')
                    fixed_prompt = expl
                    ivy_source = None
                else:
                    print(stderr,file=sys.stderr)
                    sys.exit(rc)

    print ("\n\nIteration limit reached")

if __name__ == "__main__":
    main()
