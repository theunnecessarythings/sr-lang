#!/usr/bin/env bash
set -euo pipefail

IMAGE_TAG="${1:-sr-lang-release:ubuntu22.04}"

docker build -f Dockerfile.release -t "$IMAGE_TAG" .

echo "Built image: $IMAGE_TAG"
