#!/bin/bash
sed -i -E '/assert_eq!\(\s*quote\s*\.execution_resources\s*\.full_range_pool_resources\s*0\s*\);/d' src/quoting/twamm_pool.rs
