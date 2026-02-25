import csv
import sys

def main():
    mismatches = []
    errors = []
    num_z3_calls = 0
    num_formulas = 0

    reader = csv.DictReader(sys.stdin)

    for row in reader:
        was_z3_used = row.get("z3_used", "false") == "true"
        if was_z3_used:
            num_z3_calls += 1
        num_formulas += 1

        status = row.get("status", "").strip()

        if status == "MISMATCH":
            mismatches.append(row)
        elif status == "ERROR":
            errors.append(row)

    print("=" * 80)
    print(f"Total formulas: {num_formulas}")
    print(f"Total backend calls: {num_z3_calls}")
    print(f"Total mismatches: {len(mismatches)}")
    print(f"Total errors:     {len(errors)}")
    print("=" * 80)

    for row in mismatches:
        print("\n--- MISMATCH --------------------------------------------------------")
        print(f"Index:       {row.get('index', '')}")
        print(f"Expected:    {row.get('expected', '')}")
        print(f"Actual:      {row.get('actual', '')}")
        print(f"Formula:     {row.get('formula', '')}")
        print(f"Model:       {row.get('model', '')}")
        print(f"Substituted: {row.get('substituted', '')}")
        print(f"Error:       {row.get('error', '')}")
        print("-" * 80)

    for row in errors:
        print("\n--- ERROR -----------------------------------------------------------")
        print(f"Index:       {row.get('index', '')}")
        print(f"Expected:    {row.get('expected', '')}")
        print(f"Actual:      {row.get('actual', '')}")
        print(f"Formula:     {row.get('formula', '')}")
        print(f"Error:       {row.get('error', '')}")
        print("-" * 80)


if __name__ == "__main__":
    main()
