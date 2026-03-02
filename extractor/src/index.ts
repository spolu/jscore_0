#!/usr/bin/env node
/**
 * CLI entry point for JSCore₀ extractor.
 *
 * Commands:
 *   extract [files...]  — emit .lean files from annotated TypeScript
 *   verify [files...]   — extract + lake build
 *   coverage [files...] — report sorry/success per function
 */

import { extractFiles, ExtractionResult } from "./extract";
import { execSync } from "child_process";
import * as path from "path";
import * as fs from "fs";

const args = process.argv.slice(2);
const command = args[0];

function usage(): void {
  console.log(`Usage: jscore <command> [options] [files...]

Commands:
  extract   Extract annotated TS functions to Lean files
  verify    Extract and run lake build to check proofs
  coverage  Show sorry/proved status per function

Options:
  --out-dir <dir>      Output directory for .lean files (default: ./generated)
  --tsconfig <path>    Path to tsconfig.json
  --lean-dir <dir>     Lean project directory (default: ../jscore)
`);
}

if (!command || command === "--help" || command === "-h") {
  usage();
  process.exit(0);
}

// Parse options
let outDir = "./generated";
let tsConfigPath: string | undefined;
let leanDir = path.resolve(__dirname, "../../jscore");
const files: string[] = [];

for (let i = 1; i < args.length; i++) {
  switch (args[i]) {
    case "--out-dir":
      outDir = args[++i];
      break;
    case "--tsconfig":
      tsConfigPath = args[++i];
      break;
    case "--lean-dir":
      leanDir = args[++i];
      break;
    default:
      files.push(args[i]);
  }
}

if (files.length === 0) {
  console.error("Error: no input files specified.");
  process.exit(1);
}

// Resolve paths
const resolvedFiles = files.map((f) => path.resolve(f));
const resolvedOutDir = path.resolve(outDir);

switch (command) {
  case "extract":
    runExtract(resolvedFiles, resolvedOutDir, tsConfigPath);
    break;
  case "verify":
    runVerify(resolvedFiles, resolvedOutDir, tsConfigPath, leanDir);
    break;
  case "coverage":
    runCoverage(resolvedFiles, resolvedOutDir, tsConfigPath);
    break;
  default:
    console.error(`Unknown command: ${command}`);
    usage();
    process.exit(1);
}

function runExtract(
  filePaths: string[],
  outputDir: string,
  tsConfig?: string
): ExtractionResult[] {
  const results = extractFiles(filePaths, outputDir, tsConfig);

  for (const r of results) {
    const status = r.hasSorry ? "sorry" : "ok";
    const outPath = path.join(outputDir, `${r.functionName}.lean`);
    console.log(
      `  ${r.functionName}: ${status} (${r.invariantCount} invariants, ${r.requiresCount} requires) → ${outPath}`
    );
  }

  console.log(`\nExtracted ${results.length} function(s) to ${outputDir}`);
  return results;
}

function runVerify(
  filePaths: string[],
  outputDir: string,
  tsConfig: string | undefined,
  leanProjectDir: string
): void {
  const results = runExtract(filePaths, outputDir, tsConfig);

  if (results.length === 0) {
    console.log("No annotated functions found.");
    return;
  }

  console.log(`\nRunning lake build in ${leanProjectDir}...`);

  try {
    execSync("lake build", {
      cwd: leanProjectDir,
      stdio: "inherit",
    });
    console.log("\nAll proofs verified successfully.");
  } catch {
    console.error("\nProof verification failed.");
    process.exit(1);
  }
}

function runCoverage(
  filePaths: string[],
  outputDir: string,
  tsConfig?: string
): void {
  const results = runExtract(filePaths, outputDir, tsConfig);

  if (results.length === 0) {
    console.log("No annotated functions found.");
    return;
  }

  let totalInvariants = 0;
  let totalSorry = 0;
  let totalProved = 0;

  console.log("\n--- Coverage Report ---\n");

  for (const r of results) {
    totalInvariants += r.invariantCount;
    if (r.hasSorry) {
      totalSorry++;
    } else {
      totalProved++;
    }

    const icon = r.hasSorry ? "[ ]" : "[x]";
    console.log(
      `${icon} ${r.functionName} — ${r.invariantCount} invariant(s), ${r.requiresCount} require(s)`
    );
  }

  console.log(`\nTotal: ${results.length} functions`);
  console.log(`  Proved:  ${totalProved}`);
  console.log(`  Sorry:   ${totalSorry}`);
  console.log(
    `  Coverage: ${results.length > 0 ? ((totalProved / results.length) * 100).toFixed(1) : 0}%`
  );
}
