import csv
import sys

def main():
    mismatches = []
    errors = []

    reader = csv.DictReader(sys.stdin)

    for row in reader:
        status = row.get("status", "").strip()

        if status == "MISMATCH":
            mismatches.append(row)
        elif status == "ERROR":
            errors.append(row)

    print("=" * 80)
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
