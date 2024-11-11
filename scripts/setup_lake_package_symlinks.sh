#!/usr/bin/env bash

# Create the target directory .lake/packages if it doesn't already exist
mkdir -p .lake/packages

# Loop through each package in the source directory ../.lake/packages
for package_path in ../.lake/packages/*; do
  # Extract the package name from the full path
  package=$(basename "$package_path")

  # Create a symbolic link to the package in .lake/packages,
  # pointing back to the original package location
  ln -s "../../../.lake/packages/$package" ".lake/packages/$package"
done
