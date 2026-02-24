FROM python:3.12-slim

WORKDIR /app

# Install system deps for psycopg (PostgreSQL)
RUN apt-get update && apt-get install -y --no-install-recommends \
    libpq-dev gcc \
    && rm -rf /var/lib/apt/lists/*

# Copy everything (README.md, src/, pyproject.toml — all needed for hatchling)
COPY . .

# Install Python deps
RUN pip install --no-cache-dir '.[api]'

# Default port
ENV PORT=8000

CMD uvicorn kovrin.api.server:app --host 0.0.0.0 --port ${PORT}
