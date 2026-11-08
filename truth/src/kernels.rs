//! Set and graph primitives vendored from the owner's `rust-kernels`
//! workspace (<https://github.com/moritzbrantner/rust-kernels>, revision
//! d8a68f926b9b2bc00caeb701384d88a3827ecdc7, MIT license):
//! `similarity-kernels` (`sorted_unique_intersection_count`,
//! `jaccard_similarity_sorted_unique`, `sorted_unique_union`) and
//! `graph-kernels` (`breadth_first`). They are copied rather than depended on
//! so the repository keeps no runtime dependency on another repository
//! (AGENTS.md invariant 19). The set functions are unchanged; `reachable`
//! adapts `breadth_first` to return the set reached by one or more edges.
use std::{cmp::Ordering, collections::BTreeSet};

/// Counts the intersection of two strictly sorted, duplicate-free slices.
pub fn sorted_unique_intersection_count<T: Ord>(left: &[T], right: &[T]) -> usize {
    let (mut count, mut i, mut j) = (0, 0, 0);
    while i < left.len() && j < right.len() {
        match left[i].cmp(&right[j]) {
            Ordering::Less => i += 1,
            Ordering::Greater => j += 1,
            Ordering::Equal => {
                count += 1;
                i += 1;
                j += 1;
            }
        }
    }
    count
}

/// Exact Jaccard similarity of two sorted-unique sets; two empty sets are
/// identical (similarity `1.0`).
pub fn jaccard_similarity_sorted_unique<T: Ord>(left: &[T], right: &[T]) -> f64 {
    if left.is_empty() && right.is_empty() {
        return 1.0;
    }
    let intersection = sorted_unique_intersection_count(left, right);
    intersection as f64 / (left.len() + right.len() - intersection) as f64
}

/// Union of two strictly sorted, duplicate-free slices.
pub fn sorted_unique_union<T: Clone + Ord>(left: &[T], right: &[T]) -> Vec<T> {
    let mut output = Vec::with_capacity(left.len() + right.len());
    let (mut i, mut j) = (0, 0);
    while i < left.len() && j < right.len() {
        match left[i].cmp(&right[j]) {
            Ordering::Less => {
                output.push(left[i].clone());
                i += 1;
            }
            Ordering::Greater => {
                output.push(right[j].clone());
                j += 1;
            }
            Ordering::Equal => {
                output.push(left[i].clone());
                i += 1;
                j += 1;
            }
        }
    }
    output.extend(left[i..].iter().cloned());
    output.extend(right[j..].iter().cloned());
    output
}

/// Every node reachable from `start` by one or more edges (breadth first).
pub fn reachable<N, I, F>(start: N, mut neighbors: F) -> BTreeSet<N>
where
    N: Clone + Ord,
    I: IntoIterator<Item = N>,
    F: FnMut(&N) -> I,
{
    let mut seen = BTreeSet::new();
    let mut frontier = std::collections::VecDeque::from([start]);
    while let Some(node) = frontier.pop_front() {
        for next in neighbors(&node) {
            if seen.insert(next.clone()) {
                frontier.push_back(next);
            }
        }
    }
    seen
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn jaccard_and_union() {
        assert_eq!(jaccard_similarity_sorted_unique::<u32>(&[], &[]), 1.0);
        assert_eq!(
            jaccard_similarity_sorted_unique(&[1, 2, 3], &[2, 3, 4]),
            0.5
        );
        assert_eq!(sorted_unique_union(&[1, 3], &[2, 3]), vec![1, 2, 3]);
    }

    #[test]
    fn reachable_excludes_unreached_and_handles_cycles() {
        let edges = |n: &u32| match n {
            1 => vec![2],
            2 => vec![3, 1],
            _ => vec![],
        };
        assert_eq!(reachable(1, edges), BTreeSet::from([1, 2, 3]));
        assert_eq!(reachable(3, edges), BTreeSet::new());
    }
}
