"""Allow running as: python -m kovrin.schema"""

from kovrin.schema.exporter import main

if __name__ == "__main__":
    main()
else:
    # When invoked via -m kovrin.schema, __name__ is "__main__" above.
    # This branch handles direct imports.
    main()
