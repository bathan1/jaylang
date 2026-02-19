import csv
import sys

def main(filename):
    mismatches = []
    errors = []

    with open(filename, newline="", encoding="utf-8") as f:
        reader = csv.DictReader(f)
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
        print(f"Index:      {row['index']}")
        print(f"Expected:   {row['expected']}")
        print(f"Actual:     {row['actual']}")
        print(f"Formula:    {row['formula']}")
        print(f"Model:      {row['model']}")
        print(f"Substituted:{row['substituted']}")
        print(f"Error:      {row['error']}")
        print("-" * 80)

    for row in errors:
        print("\n--- ERROR -----------------------------------------------------------")
        print(f"Index:      {row['index']}")
        print(f"Expected:   {row['expected']}")
        print(f"Actual:     {row['actual']}")
        print(f"Formula:    {row['formula']}")
        print(f"Error:      {row['error']}")
        print("-" * 80)


if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python analyze_results.py results.csv")
        sys.exit(1)

    main(sys.argv[1])

