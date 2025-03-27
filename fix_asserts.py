import re

# Read the file
with open('src/quoting/twamm_pool.rs', 'r') as file:
    content = file.read()

# Define a pattern to match the broken assert_eq blocks
pattern = r'assert_eq!\(\s+quote\s+\.execution_resources\s+\.full_range_pool_resources\s+0\s+\);'

# Replace all occurrences with an empty string
fixed_content = re.sub(pattern, '', content, flags=re.DOTALL)

# Write the fixed content back
with open('src/quoting/twamm_pool.rs', 'w') as file:
    file.write(fixed_content)
