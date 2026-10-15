use std::collections::{BTreeMap, BTreeSet, HashSet};

#[derive(Clone, Debug)]
struct Poset {
    /// Zero-based Hessenberg function: i <= h[i], and h is nondecreasing.
    h: Vec<usize>,
}

impl Poset {
    fn n(&self) -> usize {
        self.h.len()
    }

    fn lt(&self, a: usize, b: usize) -> bool {
        a < b && b > self.h[a]
    }

    fn edge(&self, a: usize, b: usize) -> bool {
        let (a, b) = if a < b { (a, b) } else { (b, a) };
        a < b && b <= self.h[a]
    }

    fn code(&self) -> Vec<usize> {
        self.h.iter().map(|x| x + 1).collect()
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
struct Triple {
    lambda: Vec<usize>,
    pi: Vec<usize>,
    q: Vec<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct State {
    a: Vec<usize>,
    triple: Triple,
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
struct Target {
    lambda: Vec<usize>,
    t: Vec<usize>,
    q: Vec<usize>,
}

#[derive(Clone, Debug)]
struct SwEvent {
    row: usize,
    col: usize,
    normalize_swaps: Vec<usize>,
}

#[derive(Clone, Debug)]
enum TraceEvent {
    Sw(SwEvent),
    InverseKostka {
        nu: Vec<usize>,
        from: Triple,
        to: Triple,
        local: Vec<InverseKostkaEvent>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct AcmState {
    /// An immaculate tableau, with positive entries, stored row by row.
    rows: Vec<Vec<usize>>,
    /// The tunnel-hook permutation in zero-based one-line notation.
    sigma: Vec<usize>,
}

#[derive(Clone, Debug)]
enum InverseKostkaEvent {
    Psi {
        k: usize,
        source_row: usize,
        target_row: usize,
        inserted_row: bool,
        deleted_row: bool,
    },
    Theta {
        row: usize,
        col: usize,
    },
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum InverseKostkaTraceLetter {
    Psi {
        k: usize,
        source_row: usize,
        target_row: usize,
        inserted_row: bool,
        deleted_row: bool,
    },
    Theta {
        row: usize,
        col: usize,
    },
}

type TraceCoordinate = (Vec<usize>, Vec<usize>, Vec<InverseKostkaTraceLetter>);

fn inverse_kostka_word(trace: &[TraceEvent]) -> Vec<InverseKostkaTraceLetter> {
    trace
        .iter()
        .filter_map(|event| {
            let TraceEvent::InverseKostka { local, .. } = event else {
                return None;
            };
            Some(local.iter().map(|event| match event {
                InverseKostkaEvent::Psi {
                    k,
                    source_row,
                    target_row,
                    inserted_row,
                    deleted_row,
                } => InverseKostkaTraceLetter::Psi {
                    k: *k,
                    source_row: *source_row,
                    target_row: *target_row,
                    inserted_row: *inserted_row,
                    deleted_row: *deleted_row,
                },
                InverseKostkaEvent::Theta { row, col } => InverseKostkaTraceLetter::Theta {
                    row: *row,
                    col: *col,
                },
            }))
        })
        .flatten()
        .collect()
}

#[derive(Clone, Debug)]
struct Catalog {
    positive: Vec<Triple>,
    negative: Vec<Triple>,
}

fn natural_unit_interval_orders(n: usize) -> Vec<Poset> {
    fn recurse(n: usize, i: usize, previous: usize, h: &mut Vec<usize>, out: &mut Vec<Poset>) {
        if i == n {
            out.push(Poset { h: h.clone() });
            return;
        }
        for value in i.max(previous)..n {
            h.push(value);
            recurse(n, i + 1, value, h, out);
            h.pop();
        }
    }
    let mut out = Vec::new();
    recurse(n, 0, 0, &mut Vec::new(), &mut out);
    out
}

fn partitions(n: usize) -> Vec<Vec<usize>> {
    fn recurse(remaining: usize, cap: usize, current: &mut Vec<usize>, out: &mut Vec<Vec<usize>>) {
        if remaining == 0 {
            out.push(current.clone());
            return;
        }
        for part in (1..=remaining.min(cap)).rev() {
            current.push(part);
            recurse(remaining - part, part, current, out);
            current.pop();
        }
    }
    let mut out = Vec::new();
    recurse(n, n, &mut Vec::new(), &mut out);
    out
}

fn compositions(n: usize) -> Vec<Vec<usize>> {
    fn recurse(remaining: usize, current: &mut Vec<usize>, out: &mut Vec<Vec<usize>>) {
        if remaining == 0 {
            out.push(current.clone());
            return;
        }
        for part in 1..=remaining {
            current.push(part);
            recurse(remaining - part, current, out);
            current.pop();
        }
    }
    let mut out = Vec::new();
    recurse(n, &mut Vec::new(), &mut out);
    out
}

fn permutations(n: usize) -> Vec<Vec<usize>> {
    fn recurse(
        n: usize,
        used: &mut Vec<bool>,
        current: &mut Vec<usize>,
        out: &mut Vec<Vec<usize>>,
    ) {
        if current.len() == n {
            out.push(current.clone());
            return;
        }
        for value in 0..n {
            if !used[value] {
                used[value] = true;
                current.push(value);
                recurse(n, used, current, out);
                current.pop();
                used[value] = false;
            }
        }
    }
    let mut out = Vec::new();
    recurse(n, &mut vec![false; n], &mut Vec::new(), &mut out);
    out
}

fn permutation_sign(pi: &[usize]) -> i8 {
    let inversions = (0..pi.len())
        .flat_map(|i| (i + 1..pi.len()).map(move |j| (i, j)))
        .filter(|&(i, j)| pi[i] > pi[j])
        .count();
    if inversions % 2 == 0 {
        1
    } else {
        -1
    }
}

fn alpha(lambda: &[usize], pi: &[usize]) -> Option<Vec<usize>> {
    let n = pi.len();
    let mut padded = lambda.to_vec();
    padded.resize(n, 0);
    let mut result = Vec::with_capacity(n);
    for i in 0..n {
        let value = padded[pi[i]] as isize - pi[i] as isize + i as isize;
        if value < 0 {
            return None;
        }
        result.push(value as usize);
    }
    Some(result)
}

fn decreasing_rearrangement(composition: &[usize]) -> Vec<usize> {
    let mut result = composition.to_vec();
    result.sort_unstable_by(|a, b| b.cmp(a));
    while result.last() == Some(&0) {
        result.pop();
    }
    result
}

fn shape(colors: &[usize], rows: usize) -> Vec<usize> {
    let mut result = vec![0; rows];
    for &color in colors {
        result[color] += 1;
    }
    result
}

fn packed_proper_colorings(poset: &Poset) -> Vec<Vec<usize>> {
    fn recurse(
        poset: &Poset,
        k: usize,
        vertex: usize,
        colors: &mut Vec<usize>,
        used: &mut Vec<usize>,
        out: &mut Vec<Vec<usize>>,
    ) {
        if vertex == poset.n() {
            if used.iter().all(|&count| count > 0) {
                out.push(colors.clone());
            }
            return;
        }
        for color in 0..k {
            if (0..vertex).any(|other| poset.edge(other, vertex) && colors[other] == color) {
                continue;
            }
            colors.push(color);
            used[color] += 1;
            recurse(poset, k, vertex + 1, colors, used, out);
            used[color] -= 1;
            colors.pop();
        }
    }

    let mut out = Vec::new();
    for k in 1..=poset.n() {
        recurse(poset, k, 0, &mut Vec::new(), &mut vec![0; k], &mut out);
    }
    out
}

fn is_kim_pylyavskyy_eligible(poset: &Poset) -> bool {
    // Proposition 3.10: eligibility is equivalent to no element climbing a
    // ladder.  In a natural labeling, a sorted ladder has adjacent elements
    // incomparable and all elements at distance at least two comparable.
    let n = poset.n();
    for mask in 0usize..(1usize << n) {
        let ladder: Vec<usize> = (0..n).filter(|&v| mask & (1 << v) != 0).collect();
        if ladder.len() < 3 {
            continue;
        }
        let is_ladder = (0..ladder.len()).all(|i| {
            (i + 1..ladder.len()).all(|j| {
                if j == i + 1 {
                    !poset.lt(ladder[i], ladder[j])
                } else {
                    poset.lt(ladder[i], ladder[j])
                }
            })
        });
        if !is_ladder {
            continue;
        }
        if (0..n).any(|x| {
            mask & (1 << x) == 0 && poset.lt(ladder[0], x) && poset.lt(x, *ladder.last().unwrap())
        }) {
            return false;
        }
    }
    true
}

fn asc(poset: &Poset, colors: &[usize]) -> usize {
    (0..poset.n())
        .flat_map(|i| (i + 1..poset.n()).map(move |j| (i, j)))
        .filter(|&(i, j)| poset.edge(i, j) && colors[i] < colors[j])
        .count()
}

fn des(poset: &Poset, colors: &[usize]) -> usize {
    (0..poset.n())
        .flat_map(|i| (i + 1..poset.n()).map(move |j| (i, j)))
        .filter(|&(i, j)| poset.edge(i, j) && colors[i] > colors[j])
        .count()
}

fn psi(poset: &Poset, colors: &mut [usize], row: usize) {
    let eligible: Vec<usize> = (0..poset.n())
        .filter(|&v| colors[v] == row || colors[v] == row + 1)
        .collect();
    let eligible_set: HashSet<usize> = eligible.iter().copied().collect();
    let mut seen = HashSet::new();
    for start in eligible {
        if !seen.insert(start) {
            continue;
        }
        let mut stack = vec![start];
        let mut component = vec![start];
        while let Some(v) = stack.pop() {
            for w in 0..poset.n() {
                if eligible_set.contains(&w) && poset.edge(v, w) && seen.insert(w) {
                    stack.push(w);
                    component.push(w);
                }
            }
        }
        if component.len() % 2 == 1 {
            for v in component {
                colors[v] = if colors[v] == row { row + 1 } else { row };
            }
        }
    }
}

fn normalization_swaps(composition: &[usize]) -> Vec<usize> {
    let mut weights = composition.to_vec();
    let mut swaps = Vec::new();
    while let Some(row) =
        (0..weights.len().saturating_sub(1)).find(|&row| weights[row] < weights[row + 1])
    {
        weights.swap(row, row + 1);
        swaps.push(row);
    }
    swaps
}

fn normalize(poset: &Poset, colors: &[usize], composition: &[usize]) -> (Vec<usize>, Vec<usize>) {
    let swaps = normalization_swaps(composition);
    let mut result = colors.to_vec();
    for &row in &swaps {
        psi(poset, &mut result, row);
    }
    (result, swaps)
}

fn denormalize(poset: &Poset, colors: &[usize], composition: &[usize]) -> Vec<usize> {
    let mut result = colors.to_vec();
    for &row in normalization_swaps(composition).iter().rev() {
        psi(poset, &mut result, row);
    }
    result
}

fn reversal_swaps(k: usize) -> Vec<usize> {
    let mut tokens: Vec<usize> = (0..k).rev().collect();
    let mut swaps = Vec::new();
    for target_position in 0..k {
        let mut position = tokens
            .iter()
            .position(|&token| token == target_position)
            .unwrap();
        while position > target_position {
            tokens.swap(position - 1, position);
            swaps.push(position - 1);
            position -= 1;
        }
    }
    swaps
}

fn orient_asc_to_des(poset: &Poset, colors: &[usize], k: usize) -> Vec<usize> {
    let mut result: Vec<usize> = colors.iter().map(|&color| k - 1 - color).collect();
    for row in reversal_swaps(k) {
        psi(poset, &mut result, row);
    }
    result
}

fn undo_asc_to_des(poset: &Poset, colors: &[usize], k: usize) -> Vec<usize> {
    let mut result = colors.to_vec();
    for &row in reversal_swaps(k).iter().rev() {
        psi(poset, &mut result, row);
    }
    result.iter().map(|&color| k - 1 - color).collect()
}

fn rows(colors: &[usize], row_count: usize) -> Vec<Vec<usize>> {
    let mut result = vec![Vec::new(); row_count];
    for (vertex, &row) in colors.iter().enumerate() {
        result[row].push(vertex);
    }
    result
}

fn raw_sw(
    poset: &Poset,
    colors: &[usize],
    pi: &[usize],
) -> Option<(Vec<usize>, Vec<usize>, usize, usize)> {
    let row_count = pi.len();
    let array = rows(colors, row_count);
    let max_col = array.iter().map(Vec::len).max().unwrap_or(0);
    let mut bad = None;
    'columns: for col in 0..max_col {
        for lower_row in (1..row_count).rev() {
            if col >= array[lower_row].len() {
                continue;
            }
            let lower = array[lower_row][col];
            if col >= array[lower_row - 1].len() || poset.lt(lower, array[lower_row - 1][col]) {
                bad = Some((lower_row - 1, col));
                break 'columns;
            }
        }
    }
    let (row, col) = bad?;

    let suffix: Vec<usize> = array[row][col..]
        .iter()
        .chain(array[row + 1].iter().skip(col + 1))
        .copied()
        .collect();
    let suffix_set: HashSet<usize> = suffix.iter().copied().collect();
    let mut result = colors.to_vec();
    let mut seen = HashSet::new();
    for start in suffix {
        if !seen.insert(start) {
            continue;
        }
        let mut stack = vec![start];
        let mut component = vec![start];
        while let Some(v) = stack.pop() {
            for w in 0..poset.n() {
                if suffix_set.contains(&w) && poset.edge(v, w) && seen.insert(w) {
                    stack.push(w);
                    component.push(w);
                }
            }
        }
        if component.len() % 2 == 1 {
            for v in component {
                result[v] = if result[v] == row { row + 1 } else { row };
            }
        }
    }
    let mut new_pi = pi.to_vec();
    new_pi.swap(row, row + 1);
    Some((result, new_pi, row, col))
}

fn sw_conjugate(poset: &Poset, state: &State) -> Option<(State, SwEvent)> {
    let old_alpha = alpha(&state.triple.lambda, &state.triple.pi).unwrap();
    let raw = denormalize(poset, &state.a, &old_alpha);
    let (new_raw, new_pi, row, col) = raw_sw(poset, &raw, &state.triple.pi)?;
    let new_alpha = alpha(&state.triple.lambda, &new_pi).unwrap();
    assert_eq!(shape(&new_raw, new_alpha.len()), new_alpha);
    let (new_a, normalize_swaps) = normalize(poset, &new_raw, &new_alpha);
    let mut triple = state.triple.clone();
    triple.pi = new_pi;
    Some((
        State { a: new_a, triple },
        SwEvent {
            row,
            col,
            normalize_swaps,
        },
    ))
}

fn cell_coordinates(lambda: &[usize]) -> Vec<(usize, usize)> {
    let mut coordinates = Vec::new();
    for (row, &length) in lambda.iter().enumerate() {
        for col in 0..length {
            coordinates.push((row, col));
        }
    }
    coordinates
}

fn ssyts(lambda: &[usize], mu: &[usize]) -> Vec<Vec<usize>> {
    fn recurse(
        lambda: &[usize],
        coordinates: &[(usize, usize)],
        index: usize,
        remaining: &mut Vec<usize>,
        entries: &mut Vec<usize>,
        out: &mut Vec<Vec<usize>>,
    ) {
        if index == coordinates.len() {
            out.push(entries.clone());
            return;
        }
        let (row, col) = coordinates[index];
        for value in 0..remaining.len() {
            if remaining[value] == 0 {
                continue;
            }
            if col > 0 && entries[index - 1] > value {
                continue;
            }
            if row > 0 && col < lambda[row - 1] {
                let above_index: usize = lambda[..row - 1].iter().sum::<usize>() + col;
                if entries[above_index] >= value {
                    continue;
                }
            }
            remaining[value] -= 1;
            entries.push(value);
            recurse(lambda, coordinates, index + 1, remaining, entries, out);
            entries.pop();
            remaining[value] += 1;
        }
    }
    let coordinates = cell_coordinates(lambda);
    let mut out = Vec::new();
    recurse(
        lambda,
        &coordinates,
        0,
        &mut mu.to_vec(),
        &mut Vec::new(),
        &mut out,
    );
    out
}

fn inverse_permutation(permutation: &[usize]) -> Vec<usize> {
    let mut inverse = vec![0; permutation.len()];
    for (index, &value) in permutation.iter().enumerate() {
        inverse[value] = index;
    }
    inverse
}

fn entries_to_rows(lambda: &[usize], entries: &[usize], add_one: bool) -> Vec<Vec<usize>> {
    let mut rows = Vec::with_capacity(lambda.len());
    let mut offset = 0;
    for &length in lambda {
        let mut row = entries[offset..offset + length].to_vec();
        if add_one {
            for value in &mut row {
                *value += 1;
            }
        }
        rows.push(row);
        offset += length;
    }
    assert_eq!(offset, entries.len());
    rows
}

fn rows_to_entries(rows: &[Vec<usize>], subtract_one: bool) -> Vec<usize> {
    rows.iter()
        .flatten()
        .map(|&value| if subtract_one { value - 1 } else { value })
        .collect()
}

fn bender_knuth(lambda: &[usize], entries: &[usize], value: usize) -> Vec<usize> {
    let mut rows = entries_to_rows(lambda, entries, false);
    let mut paired: Vec<Vec<bool>> = rows.iter().map(|row| vec![false; row.len()]).collect();
    for row in 0..rows.len().saturating_sub(1) {
        for col in 0..rows[row + 1].len() {
            if rows[row][col] == value && rows[row + 1][col] == value + 1 {
                paired[row][col] = true;
                paired[row + 1][col] = true;
            }
        }
    }
    for row in 0..rows.len() {
        let free: Vec<usize> = (0..rows[row].len())
            .filter(|&col| {
                !paired[row][col] && (rows[row][col] == value || rows[row][col] == value + 1)
            })
            .collect();
        let smaller = free.iter().filter(|&&col| rows[row][col] == value).count();
        let larger = free.len() - smaller;
        for (index, &col) in free.iter().enumerate() {
            rows[row][col] = if index < larger { value } else { value + 1 };
        }
    }
    rows_to_entries(&rows, false)
}

fn normalize_ssyt_content(entries: &[usize], lambda: &[usize], mu: &[usize]) -> Vec<usize> {
    let mut result = entries.to_vec();
    for value in normalization_swaps(mu) {
        result = bender_knuth(lambda, &result, value);
    }
    result
}

fn denormalize_ssyt_content(entries: &[usize], lambda: &[usize], mu: &[usize]) -> Vec<usize> {
    let mut result = entries.to_vec();
    for &value in normalization_swaps(mu).iter().rev() {
        result = bender_knuth(lambda, &result, value);
    }
    result
}

fn acm_delta(state: &AcmState) -> Vec<usize> {
    assert_eq!(state.rows.len(), state.sigma.len());
    state
        .rows
        .iter()
        .enumerate()
        .map(|(row, entries)| {
            let value = entries.len() as isize + state.sigma[row] as isize - row as isize;
            assert!(value >= 0, "negative tunnel-hook content");
            value as usize
        })
        .collect()
}

fn flattened_delta(state: &AcmState) -> Vec<usize> {
    acm_delta(state)
        .into_iter()
        .filter(|&part| part > 0)
        .collect()
}

fn is_immaculate(rows: &[Vec<usize>]) -> bool {
    !rows.is_empty()
        && rows
            .iter()
            .all(|row| !row.is_empty() && row.windows(2).all(|pair| pair[0] <= pair[1]))
        && rows.windows(2).all(|pair| pair[0][0] < pair[1][0])
}

fn bad_tableau_cell(rows: &[Vec<usize>]) -> Option<(usize, usize)> {
    let max_col = rows.iter().map(Vec::len).max().unwrap_or(0);
    for col in 1..max_col {
        for row in (1..rows.len()).rev() {
            if col < rows[row].len()
                && (col >= rows[row - 1].len() || rows[row - 1][col] >= rows[row][col])
            {
                return Some((row, col));
            }
        }
    }
    None
}

fn is_semistandard_rows(rows: &[Vec<usize>]) -> bool {
    is_immaculate(rows)
        && rows.windows(2).all(|pair| pair[0].len() >= pair[1].len())
        && bad_tableau_cell(rows).is_none()
}

fn swap_permutation_values(permutation: &mut [usize], smaller: usize) {
    for value in permutation {
        if *value == smaller {
            *value = smaller + 1;
        } else if *value == smaller + 1 {
            *value = smaller;
        }
    }
}

fn insert_fixed_point(permutation: &[usize], position: usize) -> Vec<usize> {
    let mut result: Vec<usize> = permutation
        .iter()
        .map(|&value| if value >= position { value + 1 } else { value })
        .collect();
    result.insert(position, position);
    result
}

fn remove_fixed_point(permutation: &[usize], position: usize) -> Vec<usize> {
    assert_eq!(permutation[position], position);
    permutation
        .iter()
        .enumerate()
        .filter(|&(index, _)| index != position)
        .map(|(_, &value)| if value > position { value - 1 } else { value })
        .collect()
}

fn acm_psi(state: &AcmState) -> Option<(AcmState, InverseKostkaEvent)> {
    assert!(is_immaculate(&state.rows));
    let ell = state.rows.len();
    let maximum = *state.rows.iter().flatten().max().unwrap();
    let settled_suffix =
        |k: usize| {
            (k..ell).all(|row| {
                let target = maximum as isize - ell as isize + row as isize + 1;
                target > 0
                    && state.sigma[row] == row
                    && state.rows[row]
                        .iter()
                        .all(|&entry| entry as isize == target)
                    && state.rows.iter().enumerate().all(|(other, entries)| {
                        other == row || !entries.contains(&(target as usize))
                    })
            })
        };
    let k = (0..ell)
        .find(|&candidate| settled_suffix(candidate))
        .unwrap_or(ell);
    if k == 0 {
        return None;
    }
    let moved = (maximum as isize - ell as isize + k as isize) as usize;
    assert!(moved > 0);
    let source_row = (0..ell)
        .filter(|&row| state.rows[row].contains(&moved))
        .min_by_key(|&row| state.sigma[row])
        .expect("Algorithm 4.2 selected value must occur");
    let old_content = flattened_delta(state);
    let old_sign = permutation_sign(&state.sigma);
    let mut rows = state.rows.clone();
    assert_eq!(rows[source_row].pop(), Some(moved));

    let (sigma, target_row, inserted_row, deleted_row) = if state.sigma[source_row] + 1 == k {
        rows.insert(k, vec![moved]);
        let mut sigma = insert_fixed_point(&state.sigma, k);
        swap_permutation_values(&mut sigma, k - 1);
        (sigma, k, true, false)
    } else {
        let q = state.sigma[source_row];
        let target_row = state
            .sigma
            .iter()
            .position(|&value| value == q + 1)
            .expect("q+1 must occur in a permutation");
        rows[target_row].push(moved);
        let mut sigma = state.sigma.clone();
        swap_permutation_values(&mut sigma, q);
        let deleted_row = rows[source_row].is_empty();
        if deleted_row {
            assert_eq!(source_row, k - 1);
            rows.remove(source_row);
            sigma = remove_fixed_point(&sigma, source_row);
        }
        (sigma, target_row, false, deleted_row)
    };
    let result = AcmState { rows, sigma };
    assert!(is_immaculate(&result.rows));
    assert_eq!(flattened_delta(&result), old_content);
    assert_eq!(permutation_sign(&result.sigma), -old_sign);
    Some((
        result,
        InverseKostkaEvent::Psi {
            k,
            source_row,
            target_row,
            inserted_row,
            deleted_row,
        },
    ))
}

fn acm_theta(state: &AcmState) -> (AcmState, InverseKostkaEvent) {
    assert!(is_immaculate(&state.rows));
    let (row, col) = bad_tableau_cell(&state.rows).expect("theta requires a bad cell");
    let old_partition = decreasing_rearrangement(&acm_delta(state));
    let old_sign = permutation_sign(&state.sigma);
    let upper = state.rows[row - 1].clone();
    let lower = state.rows[row].clone();
    let mut rows = state.rows.clone();
    rows[row - 1] = upper[..col]
        .iter()
        .chain(lower[col + 1..].iter())
        .copied()
        .collect();
    rows[row] = lower[..=col]
        .iter()
        .chain(upper[col..].iter())
        .copied()
        .collect();
    let mut sigma = state.sigma.clone();
    sigma.swap(row - 1, row);
    let result = AcmState { rows, sigma };
    assert!(is_immaculate(&result.rows));
    assert_eq!(bad_tableau_cell(&result.rows), Some((row, col)));
    assert_eq!(decreasing_rearrangement(&acm_delta(&result)), old_partition);
    assert_eq!(permutation_sign(&result.sigma), -old_sign);
    (result, InverseKostkaEvent::Theta { row, col })
}

fn triple_to_acm(triple: &Triple, mu: &[usize]) -> AcmState {
    let ell = triple.lambda.len();
    assert!(triple
        .pi
        .iter()
        .enumerate()
        .skip(ell)
        .all(|(index, &value)| index == value));
    let short_pi = triple.pi[..ell].to_vec();
    assert!(short_pi.iter().all(|&value| value < ell));
    let sigma = inverse_permutation(&short_pi);
    let normalized_q = normalize_ssyt_content(&triple.q, &triple.lambda, mu);
    let rows = entries_to_rows(&triple.lambda, &normalized_q, true);
    let result = AcmState { rows, sigma };
    assert!(is_semistandard_rows(&result.rows));
    result
}

fn acm_to_triple(state: &AcmState, mu: &[usize], n: usize) -> Triple {
    assert!(is_semistandard_rows(&state.rows));
    let lambda: Vec<usize> = state.rows.iter().map(Vec::len).collect();
    let short_pi = inverse_permutation(&state.sigma);
    let mut pi = short_pi;
    pi.extend(lambda.len()..n);
    let normalized_q = rows_to_entries(&state.rows, true);
    let q = denormalize_ssyt_content(&normalized_q, &lambda, mu);
    Triple { lambda, pi, q }
}

fn canonical_fixed_triple(n: usize, mu: &[usize]) -> Triple {
    let lambda = decreasing_rearrangement(mu);
    let normalized_q: Vec<usize> = lambda
        .iter()
        .enumerate()
        .flat_map(|(row, &length)| std::iter::repeat_n(row, length))
        .collect();
    let q = denormalize_ssyt_content(&normalized_q, &lambda, mu);
    Triple {
        lambda,
        pi: (0..n).collect(),
        q,
    }
}

fn replay_inverse_kostka_word(
    mu: &[usize],
    word: &[InverseKostkaTraceLetter],
) -> (Vec<usize>, Vec<usize>) {
    let initial_lambda = decreasing_rearrangement(mu);
    let mut rows: Vec<Vec<usize>> = initial_lambda
        .iter()
        .enumerate()
        .map(|(row, &length)| vec![row + 1; length])
        .collect();
    for letter in word {
        match *letter {
            InverseKostkaTraceLetter::Psi {
                k,
                source_row,
                target_row,
                inserted_row,
                deleted_row,
            } => {
                let moved = rows[source_row]
                    .pop()
                    .expect("a recorded psi source row must be nonempty");
                if inserted_row {
                    assert!(!deleted_row);
                    assert_eq!(target_row, k);
                    rows.insert(target_row, vec![moved]);
                } else {
                    rows[target_row].push(moved);
                    if deleted_row {
                        assert_eq!(source_row, k - 1);
                        assert!(rows[source_row].is_empty());
                        rows.remove(source_row);
                    }
                }
            }
            InverseKostkaTraceLetter::Theta { row, col } => {
                let upper = rows[row - 1].clone();
                let lower = rows[row].clone();
                rows[row - 1] = upper[..col]
                    .iter()
                    .chain(lower[col + 1..].iter())
                    .copied()
                    .collect();
                rows[row] = lower[..=col]
                    .iter()
                    .chain(upper[col..].iter())
                    .copied()
                    .collect();
            }
        }
    }
    assert!(is_semistandard_rows(&rows));
    let lambda: Vec<usize> = rows.iter().map(Vec::len).collect();
    let normalized_q = rows_to_entries(&rows, true);
    let q = denormalize_ssyt_content(&normalized_q, &lambda, mu);
    (lambda, q)
}

fn inverse_kostka_local(
    triple: &Triple,
    nu: &[usize],
    mu: &[usize],
) -> Option<(Triple, Vec<InverseKostkaEvent>)> {
    if decreasing_rearrangement(nu) == decreasing_rearrangement(mu) {
        assert_eq!(*triple, canonical_fixed_triple(triple.pi.len(), mu));
        return None;
    }
    let start = triple_to_acm(triple, mu);
    assert_eq!(decreasing_rearrangement(&acm_delta(&start)), nu);
    let mut state = start.clone();
    let mut events = Vec::new();
    for _ in 0..100_000 {
        let (after_psi, psi_event) =
            acm_psi(&state).expect("Algorithm 4.2 cannot fix a non-diagonal inverse-Kostka state");
        assert_eq!(acm_psi(&after_psi).unwrap().0, state);
        events.push(psi_event);
        if is_semistandard_rows(&after_psi.rows) {
            let result = acm_to_triple(&after_psi, mu, triple.pi.len());
            assert_eq!(
                decreasing_rearrangement(&alpha(&result.lambda, &result.pi).unwrap()),
                nu
            );
            assert_eq!(permutation_sign(&result.pi), -permutation_sign(&triple.pi));
            return Some((result, events));
        }
        let (after_theta, theta_event) = acm_theta(&after_psi);
        assert_eq!(acm_theta(&after_theta).0, after_psi);
        events.push(theta_event);
        state = after_theta;
    }
    panic!("Allen--Celano--Mason path exceeded safety bound");
}

fn build_catalog(n: usize, nu: &[usize], mu: &[usize]) -> Catalog {
    let nu_partition = decreasing_rearrangement(nu);
    let mut positive = Vec::new();
    let mut negative = Vec::new();
    let all_permutations = permutations(n);
    for lambda in partitions(n) {
        let tableaux = ssyts(&lambda, mu);
        if tableaux.is_empty() {
            continue;
        }
        for pi in &all_permutations {
            let Some(composition) = alpha(&lambda, pi) else {
                continue;
            };
            if decreasing_rearrangement(&composition) != nu_partition {
                continue;
            }
            for q in &tableaux {
                let triple = Triple {
                    lambda: lambda.clone(),
                    pi: pi.clone(),
                    q: q.clone(),
                };
                if permutation_sign(pi) > 0 {
                    positive.push(triple);
                } else {
                    negative.push(triple);
                }
            }
        }
    }
    positive.sort();
    negative.sort();
    let exceptional = nu_partition == decreasing_rearrangement(mu);
    assert_eq!(positive.len(), negative.len() + usize::from(exceptional));
    Catalog { positive, negative }
}

fn p_tableaux(poset: &Poset, lambda: &[usize]) -> Vec<Vec<usize>> {
    let coordinates = cell_coordinates(lambda);
    let mut out = Vec::new();
    for entries in permutations(poset.n()) {
        let mut valid = true;
        for (index, &(row, col)) in coordinates.iter().enumerate() {
            if col > 0 && !poset.lt(entries[index - 1], entries[index]) {
                valid = false;
                break;
            }
            if row > 0 && col < lambda[row - 1] {
                let above_index = lambda[..row - 1].iter().sum::<usize>() + col;
                if poset.lt(entries[index], entries[above_index]) {
                    valid = false;
                    break;
                }
            }
        }
        if valid {
            let mut colors = vec![0; poset.n()];
            for (index, &(row, _)) in coordinates.iter().enumerate() {
                colors[entries[index]] = row;
            }
            out.push(colors);
        }
    }
    out.sort();
    out.dedup();
    out
}

fn inv_g(poset: &Poset, tableau: &[usize]) -> usize {
    des(poset, tableau)
}

fn forward_with_alphabet(
    poset: &Poset,
    coloring: &[usize],
    alphabet: usize,
) -> (Target, Vec<TraceEvent>) {
    assert!(coloring.iter().all(|&color| color < alphabet));
    let mu = shape(coloring, alphabet);
    let oriented = orient_asc_to_des(poset, coloring, alphabet);
    assert_eq!(shape(&oriented, alphabet), mu);
    assert_eq!(des(poset, &oriented), asc(poset, coloring));
    let mut padded_mu = mu.clone();
    if padded_mu.len() < poset.n() {
        padded_mu.resize(poset.n(), 0);
    }
    let (normalized, _) = normalize(poset, &oriented, &padded_mu);
    assert!(
        normalized.iter().all(|&row| row < poset.n()),
        "normalization left a nonzero empty-row gap: P={:?}, mu={mu:?}, coloring={coloring:?}, oriented={oriented:?}, normalized={normalized:?}",
        poset.code()
    );
    let triple = canonical_fixed_triple(poset.n(), &mu);
    let mut state = State {
        a: normalized,
        triple,
    };
    let mut trace = Vec::new();
    for _ in 0..100_000 {
        let Some((new_state, event)) = sw_conjugate(poset, &state) else {
            assert_eq!(permutation_sign(&state.triple.pi), 1);
            assert_eq!(state.triple.pi, (0..poset.n()).collect::<Vec<_>>());
            return (
                Target {
                    lambda: state.triple.lambda,
                    t: state.a,
                    q: state.triple.q,
                },
                trace,
            );
        };
        assert_eq!(des(poset, &new_state.a), des(poset, &state.a));
        assert_eq!(
            sw_conjugate(poset, &new_state)
                .expect("SW conjugate must reverse its own nonfixed move")
                .0,
            state
        );
        trace.push(TraceEvent::Sw(event));
        state = new_state;
        let nu = decreasing_rearrangement(&shape(&state.a, poset.n()));
        let old = state.triple.clone();
        let (partner, local) = inverse_kostka_local(&state.triple, &nu, &mu)
            .expect("negative state cannot be fixed by inverse-Kostka involution");
        state.triple = partner;
        assert_eq!(
            inverse_kostka_local(&state.triple, &nu, &mu)
                .expect("local inverse-Kostka move must reverse itself")
                .0,
            old
        );
        trace.push(TraceEvent::InverseKostka {
            nu,
            from: old,
            to: state.triple.clone(),
            local,
        });
    }
    panic!("Garsia--Milne forward path exceeded safety bound");
}

fn forward(poset: &Poset, coloring: &[usize]) -> (Target, Vec<TraceEvent>) {
    forward_with_alphabet(poset, coloring, 1 + *coloring.iter().max().unwrap())
}

fn reverse(poset: &Poset, target: &Target, mu: &[usize]) -> Vec<usize> {
    let n = poset.n();
    let mut pi: Vec<usize> = (0..n).collect();
    let mut state = State {
        a: target.t.clone(),
        triple: Triple {
            lambda: target.lambda.clone(),
            pi: std::mem::take(&mut pi),
            q: target.q.clone(),
        },
    };
    for _ in 0..100_000 {
        let nu = decreasing_rearrangement(&shape(&state.a, n));
        let Some((partner, _)) = inverse_kostka_local(&state.triple, &nu, mu) else {
            let mut padded_mu = mu.to_vec();
            if padded_mu.len() < n {
                padded_mu.resize(n, 0);
            }
            let oriented = denormalize(poset, &state.a, &padded_mu);
            return undo_asc_to_des(poset, &oriented, mu.len());
        };
        state.triple = partner;
        state = sw_conjugate(poset, &state)
            .expect("nonfixed inverse-Kostka state must move under SW")
            .0;
    }
    panic!("Garsia--Milne reverse path exceeded safety bound");
}

fn target_fiber(poset: &Poset, mu: &[usize]) -> Vec<Target> {
    let mut out = Vec::new();
    for lambda in partitions(poset.n()) {
        for t in p_tableaux(poset, &lambda) {
            for q in ssyts(&lambda, mu) {
                out.push(Target {
                    lambda: lambda.clone(),
                    t: t.clone(),
                    q,
                });
            }
        }
    }
    out.sort();
    out
}

fn crystal_on_target(target: &Target, color: usize, raising: bool) -> Option<Target> {
    let mut minus = Vec::new();
    let mut plus = Vec::new();
    let mut row_offsets = Vec::with_capacity(target.lambda.len());
    let mut offset = 0;
    for &length in &target.lambda {
        row_offsets.push(offset);
        offset += length;
    }
    for row in (0..target.lambda.len()).rev() {
        for col in 0..target.lambda[row] {
            let position = row_offsets[row] + col;
            if target.q[position] == color + 1 {
                minus.push(position);
            } else if target.q[position] == color && minus.pop().is_none() {
                plus.push(position);
            }
        }
    }
    let position = if raising {
        *minus.first()?
    } else {
        *plus.last()?
    };
    let mut result = target.clone();
    if raising {
        result.q[position] -= 1;
    } else {
        result.q[position] += 1;
    }
    assert!(is_semistandard_rows(&entries_to_rows(
        &result.lambda,
        &result.q,
        true
    )));
    Some(result)
}

/// The transported Kashiwara operator on proper colorings.
///
/// Colors are zero-based, so `color` denotes the simple root joining
/// `color` and `color + 1`.  The Boolean `raising` chooses `e_color` when
/// true and `f_color` when false.
fn coloring_crystal_operator(
    poset: &Poset,
    coloring: &[usize],
    alphabet: usize,
    color: usize,
    raising: bool,
) -> Option<Vec<usize>> {
    assert!(color + 1 < alphabet);
    assert!(is_proper_coloring(poset, coloring));
    let (target, _) = forward_with_alphabet(poset, coloring, alphabet);
    let moved_target = crystal_on_target(&target, color, raising)?;
    let moved_mu = shape(&moved_target.q, alphabet);
    let moved = reverse(poset, &moved_target, &moved_mu);
    assert!(is_proper_coloring(poset, &moved));
    assert_eq!(asc(poset, &moved), asc(poset, coloring));
    Some(moved)
}

fn coloring_e(
    poset: &Poset,
    coloring: &[usize],
    alphabet: usize,
    color: usize,
) -> Option<Vec<usize>> {
    coloring_crystal_operator(poset, coloring, alphabet, color, true)
}

fn coloring_f(
    poset: &Poset,
    coloring: &[usize],
    alphabet: usize,
    color: usize,
) -> Option<Vec<usize>> {
    coloring_crystal_operator(poset, coloring, alphabet, color, false)
}

fn crystal_reflection_on_target(target: &Target, alphabet: usize, color: usize) -> Target {
    assert!(color + 1 < alphabet);
    let weight = shape(&target.q, alphabet);
    let difference = weight[color] as isize - weight[color + 1] as isize;
    let raising = difference < 0;
    let mut result = target.clone();
    for _ in 0..difference.unsigned_abs() {
        result = crystal_on_target(&result, color, raising)
            .expect("a crystal reflection cannot leave its i-string");
    }
    result
}

fn coloring_reflection(
    poset: &Poset,
    coloring: &[usize],
    alphabet: usize,
    color: usize,
) -> Vec<usize> {
    let (target, _) = forward_with_alphabet(poset, coloring, alphabet);
    let reflected_target = crystal_reflection_on_target(&target, alphabet, color);
    let reflected_weight = shape(&reflected_target.q, alphabet);
    let reflected = reverse(poset, &reflected_target, &reflected_weight);
    assert!(is_proper_coloring(poset, &reflected));
    assert_eq!(asc(poset, &reflected), asc(poset, coloring));
    reflected
}

fn target_string_length(target: &Target, color: usize, raising: bool) -> usize {
    let mut length = 0;
    let mut current = target.clone();
    while let Some(next) = crystal_on_target(&current, color, raising) {
        current = next;
        length += 1;
    }
    length
}

fn highest_weight_q(lambda: &[usize]) -> Vec<usize> {
    lambda
        .iter()
        .enumerate()
        .flat_map(|(row, &length)| std::iter::repeat_n(row, length))
        .collect()
}

fn is_proper_coloring(poset: &Poset, coloring: &[usize]) -> bool {
    (0..poset.n()).all(|left| {
        (left + 1..poset.n())
            .all(|right| !poset.edge(left, right) || coloring[left] != coloring[right])
    })
}

fn proper_colorings(poset: &Poset, alphabet: usize) -> Vec<Vec<usize>> {
    fn recurse(
        poset: &Poset,
        alphabet: usize,
        vertex: usize,
        coloring: &mut Vec<usize>,
        out: &mut Vec<Vec<usize>>,
    ) {
        if vertex == poset.n() {
            out.push(coloring.clone());
            return;
        }
        for color in 0..alphabet {
            if (0..vertex)
                .any(|other| poset.edge(other, vertex) && coloring.get(other) == Some(&color))
            {
                continue;
            }
            coloring.push(color);
            recurse(poset, alphabet, vertex + 1, coloring, out);
            coloring.pop();
        }
    }

    let mut out = Vec::new();
    recurse(poset, alphabet, 0, &mut Vec::new(), &mut out);
    out
}

#[derive(Clone, Debug)]
struct CrystalVertex {
    coloring: Vec<usize>,
    image: Target,
    has_inverse_kostka_step: bool,
    inverse_kostka_word: Vec<InverseKostkaTraceLetter>,
}

#[derive(Clone, Debug)]
struct CrystalEdge {
    from: usize,
    to: usize,
    color: usize,
}

#[derive(Clone, Debug)]
struct ColoringCrystalGraph {
    vertices: Vec<CrystalVertex>,
    edges: Vec<CrystalEdge>,
}

#[derive(Default)]
struct GraphSummary {
    vertices: usize,
    edges: usize,
    components: usize,
}

impl GraphSummary {
    fn absorb(&mut self, other: Self) {
        self.vertices += other.vertices;
        self.edges += other.edges;
        self.components += other.components;
    }
}

fn coloring_crystal_graph(poset: &Poset, alphabet: usize) -> ColoringCrystalGraph {
    let colorings = proper_colorings(poset, alphabet);
    let indices: BTreeMap<Vec<usize>, usize> = colorings
        .iter()
        .cloned()
        .enumerate()
        .map(|(index, coloring)| (coloring, index))
        .collect();
    let vertices: Vec<CrystalVertex> = colorings
        .into_iter()
        .map(|coloring| {
            let (image, trace) = forward_with_alphabet(poset, &coloring, alphabet);
            let inverse_kostka_word = inverse_kostka_word(&trace);
            let (replayed_lambda, replayed_q) =
                replay_inverse_kostka_word(&shape(&coloring, alphabet), &inverse_kostka_word);
            assert_eq!(replayed_lambda, image.lambda);
            assert_eq!(replayed_q, image.q);
            CrystalVertex {
                coloring,
                image,
                has_inverse_kostka_step: !inverse_kostka_word.is_empty(),
                inverse_kostka_word,
            }
        })
        .collect();
    let mut edges = Vec::new();
    for (from, vertex) in vertices.iter().enumerate() {
        for color in 0..alphabet.saturating_sub(1) {
            let Some(moved_target) = crystal_on_target(&vertex.image, color, false) else {
                continue;
            };
            let mu = shape(&moved_target.q, alphabet);
            let moved_coloring = reverse(poset, &moved_target, &mu);
            let to = *indices
                .get(&moved_coloring)
                .expect("transported crystal edge must end at a proper coloring");
            edges.push(CrystalEdge { from, to, color });
        }
    }
    ColoringCrystalGraph { vertices, edges }
}

fn verify_coloring_crystal_graph(poset: &Poset, alphabet: usize) -> GraphSummary {
    let graph = coloring_crystal_graph(poset, alphabet);
    let mut fibers: BTreeMap<(Vec<usize>, Vec<usize>), Vec<usize>> = BTreeMap::new();
    for (index, vertex) in graph.vertices.iter().enumerate() {
        fibers
            .entry((vertex.image.lambda.clone(), vertex.image.t.clone()))
            .or_default()
            .push(index);
    }
    let mut neighbors = vec![Vec::new(); graph.vertices.len()];
    for edge in &graph.edges {
        let from = &graph.vertices[edge.from].image;
        let to = &graph.vertices[edge.to].image;
        assert_eq!(
            (from.lambda.as_slice(), from.t.as_slice()),
            (to.lambda.as_slice(), to.t.as_slice())
        );
        neighbors[edge.from].push(edge.to);
        neighbors[edge.to].push(edge.from);
    }
    let summary = GraphSummary {
        vertices: graph.vertices.len(),
        edges: graph.edges.len(),
        components: fibers.len(),
    };
    for ((lambda, t), fiber) in fibers {
        let highest: Vec<usize> = fiber
            .iter()
            .copied()
            .filter(|&index| {
                (0..alphabet.saturating_sub(1)).all(|color| {
                    crystal_on_target(&graph.vertices[index].image, color, true).is_none()
                })
            })
            .collect();
        assert_eq!(highest.len(), 1);
        assert_eq!(
            graph.vertices[highest[0]].image.q,
            highest_weight_q(&lambda)
        );
        assert_eq!(
            graph.vertices[highest[0]].coloring,
            undo_asc_to_des(poset, &t, alphabet),
            "highest-weight coloring is not the inverse orientation of T"
        );

        let fiber_set: BTreeSet<usize> = fiber.iter().copied().collect();
        let mut reached = BTreeSet::from([highest[0]]);
        let mut stack = vec![highest[0]];
        while let Some(index) = stack.pop() {
            for &next in &neighbors[index] {
                if fiber_set.contains(&next) && reached.insert(next) {
                    stack.push(next);
                }
            }
        }
        assert_eq!(reached, fiber_set, "disconnected crystal fiber for T={t:?}");
    }
    summary
}

fn crystal_graph_dot(poset: &Poset, alphabet: usize) -> String {
    let graph = coloring_crystal_graph(poset, alphabet);
    let mut dot = String::from("digraph coloring_crystal {\n  rankdir=LR;\n");
    for (index, vertex) in graph.vertices.iter().enumerate() {
        let weight = shape(&vertex.coloring, alphabet);
        dot.push_str(&format!(
            "  v{index} [label=\"{:?}\\nwt={weight:?}, asc={}\\nshape={:?}, T={:?}\"];\n",
            vertex.coloring,
            asc(poset, &vertex.coloring),
            vertex.image.lambda,
            vertex.image.t
        ));
    }
    for edge in graph.edges {
        dot.push_str(&format!(
            "  v{} -> v{} [label=\"{}\"];\n",
            edge.from,
            edge.to,
            edge.color + 1
        ));
    }
    dot.push_str("}\n");
    dot
}

#[derive(Clone, Debug)]
struct MoveWitness {
    code: Vec<usize>,
    alphabet: usize,
    color: usize,
    source: Vec<usize>,
    target: Vec<usize>,
    changed_vertices: Vec<usize>,
}

#[derive(Clone, Debug)]
struct ContextWitness {
    code: Vec<usize>,
    alphabet: usize,
    color: usize,
    weight: Vec<usize>,
    asc: usize,
    local_restriction: Vec<Option<usize>>,
    first_source: Vec<usize>,
    first_target: Option<Vec<usize>>,
    second_source: Vec<usize>,
    second_target: Option<Vec<usize>>,
}

#[derive(Default, Debug)]
struct LocalityStudy {
    first_multiple_change: Option<MoveWitness>,
    first_outside_pair_change: Option<MoveWitness>,
    first_context_dependence: Option<ContextWitness>,
}

type LocalSignature = (Vec<usize>, usize, Vec<Option<usize>>);
type LocalOutcome = (Vec<usize>, Option<Vec<usize>>);

fn two_color_restriction(coloring: &[usize], color: usize) -> Vec<Option<usize>> {
    coloring
        .iter()
        .map(|&entry| {
            if entry == color {
                Some(0)
            } else if entry == color + 1 {
                Some(1)
            } else {
                None
            }
        })
        .collect()
}

fn study_crystal_locality(max_n: usize) -> LocalityStudy {
    let mut study = LocalityStudy::default();
    for n in 1..=max_n {
        for poset in natural_unit_interval_orders(n) {
            for alphabet in 2..=usize::min(n + 1, 4) {
                let graph = coloring_crystal_graph(&poset, alphabet);
                let edge_targets: BTreeMap<(usize, usize), usize> = graph
                    .edges
                    .iter()
                    .map(|edge| ((edge.from, edge.color), edge.to))
                    .collect();
                for color in 0..alphabet - 1 {
                    let mut local_outcomes: BTreeMap<LocalSignature, LocalOutcome> =
                        BTreeMap::new();
                    for (index, vertex) in graph.vertices.iter().enumerate() {
                        let target = edge_targets
                            .get(&(index, color))
                            .map(|&to| graph.vertices[to].coloring.clone());
                        if let Some(moved) = &target {
                            let changed_vertices: Vec<usize> =
                                (0..n).filter(|&v| vertex.coloring[v] != moved[v]).collect();
                            let witness = MoveWitness {
                                code: poset.code(),
                                alphabet,
                                color,
                                source: vertex.coloring.clone(),
                                target: moved.clone(),
                                changed_vertices: changed_vertices.clone(),
                            };
                            if changed_vertices.len() > 1 && study.first_multiple_change.is_none() {
                                study.first_multiple_change = Some(witness.clone());
                            }
                            let changes_outside_pair = changed_vertices.iter().any(|&v| {
                                ![color, color + 1].contains(&vertex.coloring[v])
                                    || ![color, color + 1].contains(&moved[v])
                            });
                            if changes_outside_pair && study.first_outside_pair_change.is_none() {
                                study.first_outside_pair_change = Some(witness);
                            }
                        }

                        let local_restriction = two_color_restriction(&vertex.coloring, color);
                        let key = (
                            shape(&vertex.coloring, alphabet),
                            asc(&poset, &vertex.coloring),
                            local_restriction.clone(),
                        );
                        if let Some((first_source, first_target)) = local_outcomes.get(&key) {
                            let first_local_target = first_target
                                .as_ref()
                                .map(|value| two_color_restriction(value, color));
                            let second_local_target = target
                                .as_ref()
                                .map(|value| two_color_restriction(value, color));
                            if first_local_target != second_local_target
                                && study.first_context_dependence.is_none()
                            {
                                study.first_context_dependence = Some(ContextWitness {
                                    code: poset.code(),
                                    alphabet,
                                    color,
                                    weight: key.0.clone(),
                                    asc: key.1,
                                    local_restriction,
                                    first_source: first_source.clone(),
                                    first_target: first_target.clone(),
                                    second_source: vertex.coloring.clone(),
                                    second_target: target.clone(),
                                });
                            }
                        } else {
                            local_outcomes.insert(key, (vertex.coloring.clone(), target));
                        }
                    }
                }
                if study.first_multiple_change.is_some()
                    && study.first_outside_pair_change.is_some()
                    && study.first_context_dependence.is_some()
                {
                    return study;
                }
            }
        }
    }
    study
}

fn print_locality_study(study: &LocalityStudy) {
    if let Some(witness) = &study.first_multiple_change {
        println!(
            "first multi-vertex f_{} move: P={:?}, k={}, {:?} -> {:?}, changed={:?}",
            witness.color + 1,
            witness.code,
            witness.alphabet,
            witness.source,
            witness.target,
            witness.changed_vertices
        );
    }
    if let Some(witness) = &study.first_outside_pair_change {
        println!(
            "first f_{} move touching a color outside its pair: P={:?}, k={}, {:?} -> {:?}, changed={:?}",
            witness.color + 1,
            witness.code,
            witness.alphabet,
            witness.source,
            witness.target,
            witness.changed_vertices
        );
    }
    if let Some(witness) = &study.first_context_dependence {
        println!(
            "first two-color-context obstruction for f_{}: P={:?}, k={}, wt={:?}, asc={}, restriction={:?}; {:?} -> {:?}, but {:?} -> {:?}",
            witness.color + 1,
            witness.code,
            witness.alphabet,
            witness.weight,
            witness.asc,
            witness.local_restriction,
            witness.first_source,
            witness.first_target,
            witness.second_source,
            witness.second_target
        );
    }
}

#[derive(Clone, Debug)]
struct ReflectionDifference {
    code: Vec<usize>,
    alphabet: usize,
    color: usize,
    source: Vec<usize>,
    transported: Vec<usize>,
    odd_component_switch: Vec<usize>,
}

#[derive(Clone, Debug)]
struct BraidFailure {
    code: Vec<usize>,
    alphabet: usize,
    color: usize,
    source: Vec<usize>,
    left: Vec<usize>,
    right: Vec<usize>,
}

#[derive(Default)]
struct ReflectionStudy {
    comparisons: usize,
    matches_odd_component_switch: usize,
    bender_knuth_comparisons: usize,
    bender_knuth_matches: usize,
    bender_knuth_switch_matches: usize,
    transported_braid_tests: usize,
    transported_commutation_tests: usize,
    odd_component_braid_tests: usize,
    odd_component_braid_failures: usize,
    bender_knuth_braid_failures: usize,
    first_difference: Option<ReflectionDifference>,
    first_crystal_bender_knuth_difference: Option<ReflectionDifference>,
    first_bender_knuth_switch_difference: Option<ReflectionDifference>,
    first_odd_component_braid_failure: Option<BraidFailure>,
    first_bender_knuth_braid_failure: Option<BraidFailure>,
    first_multiple_change: Option<MoveWitness>,
    first_outside_pair_change: Option<MoveWitness>,
    first_context_dependence: Option<ContextWitness>,
}

impl ReflectionStudy {
    fn absorb(&mut self, other: Self) {
        self.comparisons += other.comparisons;
        self.matches_odd_component_switch += other.matches_odd_component_switch;
        self.bender_knuth_comparisons += other.bender_knuth_comparisons;
        self.bender_knuth_matches += other.bender_knuth_matches;
        self.bender_knuth_switch_matches += other.bender_knuth_switch_matches;
        self.transported_braid_tests += other.transported_braid_tests;
        self.transported_commutation_tests += other.transported_commutation_tests;
        self.odd_component_braid_tests += other.odd_component_braid_tests;
        self.odd_component_braid_failures += other.odd_component_braid_failures;
        self.bender_knuth_braid_failures += other.bender_knuth_braid_failures;
        if self.first_difference.is_none() {
            self.first_difference = other.first_difference;
        }
        if self.first_crystal_bender_knuth_difference.is_none() {
            self.first_crystal_bender_knuth_difference =
                other.first_crystal_bender_knuth_difference;
        }
        if self.first_bender_knuth_switch_difference.is_none() {
            self.first_bender_knuth_switch_difference = other.first_bender_knuth_switch_difference;
        }
        if self.first_odd_component_braid_failure.is_none() {
            self.first_odd_component_braid_failure = other.first_odd_component_braid_failure;
        }
        if self.first_bender_knuth_braid_failure.is_none() {
            self.first_bender_knuth_braid_failure = other.first_bender_knuth_braid_failure;
        }
        if self.first_multiple_change.is_none() {
            self.first_multiple_change = other.first_multiple_change;
        }
        if self.first_outside_pair_change.is_none() {
            self.first_outside_pair_change = other.first_outside_pair_change;
        }
        if self.first_context_dependence.is_none() {
            self.first_context_dependence = other.first_context_dependence;
        }
    }
}

fn apply_reflection_word(maps: &[Vec<usize>], start: usize, word: &[usize]) -> usize {
    word.iter().fold(start, |state, &color| maps[color][state])
}

fn study_reflections_for_poset(poset: &Poset, alphabet: usize) -> ReflectionStudy {
    let graph = coloring_crystal_graph(poset, alphabet);
    let indices: BTreeMap<Vec<usize>, usize> = graph
        .vertices
        .iter()
        .enumerate()
        .map(|(index, vertex)| (vertex.coloring.clone(), index))
        .collect();
    let roots = alphabet.saturating_sub(1);
    let mut transported = vec![vec![0; graph.vertices.len()]; roots];
    let mut odd_component = vec![vec![0; graph.vertices.len()]; roots];
    let mut tableau_bender_knuth = vec![vec![0; graph.vertices.len()]; roots];
    let mut study = ReflectionStudy::default();
    for color in 0..roots {
        for (index, vertex) in graph.vertices.iter().enumerate() {
            let reflected_target = crystal_reflection_on_target(&vertex.image, alphabet, color);
            let reflected_weight = shape(&reflected_target.q, alphabet);
            let reflected_coloring = reverse(poset, &reflected_target, &reflected_weight);
            let reflected_index = *indices
                .get(&reflected_coloring)
                .expect("a transported reflection must remain in the coloring set");
            transported[color][index] = reflected_index;
            if poset.n() <= 3 {
                assert_eq!(
                    coloring_reflection(poset, &vertex.coloring, alphabet, color),
                    reflected_coloring
                );
            }

            let mut switched = vertex.coloring.clone();
            psi(poset, &mut switched, color);
            let switched_index = *indices
                .get(&switched)
                .expect("an odd-component switch must remain a proper coloring");
            odd_component[color][index] = switched_index;

            study.comparisons += 1;
            if reflected_index == switched_index {
                study.matches_odd_component_switch += 1;
            } else if study.first_difference.is_none() {
                study.first_difference = Some(ReflectionDifference {
                    code: poset.code(),
                    alphabet,
                    color,
                    source: vertex.coloring.clone(),
                    transported: reflected_coloring,
                    odd_component_switch: switched.clone(),
                });
            }

            let bender_q = bender_knuth(&vertex.image.lambda, &vertex.image.q, color);
            study.bender_knuth_comparisons += 1;
            if reflected_target.q == bender_q {
                study.bender_knuth_matches += 1;
            }
            let mut bender_target = vertex.image.clone();
            bender_target.q = bender_q;
            let bender_weight = shape(&bender_target.q, alphabet);
            let bender_coloring = reverse(poset, &bender_target, &bender_weight);
            let bender_index = *indices
                .get(&bender_coloring)
                .expect("a transported Bender--Knuth switch must remain in the coloring set");
            tableau_bender_knuth[color][index] = bender_index;
            if reflected_index != bender_index
                && study.first_crystal_bender_knuth_difference.is_none()
            {
                study.first_crystal_bender_knuth_difference = Some(ReflectionDifference {
                    code: poset.code(),
                    alphabet,
                    color,
                    source: vertex.coloring.clone(),
                    transported: graph.vertices[reflected_index].coloring.clone(),
                    odd_component_switch: bender_coloring.clone(),
                });
            }
            if bender_index == switched_index {
                study.bender_knuth_switch_matches += 1;
            } else if study.first_bender_knuth_switch_difference.is_none() {
                study.first_bender_knuth_switch_difference = Some(ReflectionDifference {
                    code: poset.code(),
                    alphabet,
                    color,
                    source: vertex.coloring.clone(),
                    transported: bender_coloring,
                    odd_component_switch: switched,
                });
            }

            let old_weight = shape(&vertex.coloring, alphabet);
            let mut expected_weight = old_weight.clone();
            expected_weight.swap(color, color + 1);
            assert_eq!(
                shape(&graph.vertices[reflected_index].coloring, alphabet),
                expected_weight
            );
            assert_eq!(
                asc(poset, &graph.vertices[reflected_index].coloring),
                asc(poset, &vertex.coloring)
            );
        }
    }

    for color in 0..roots {
        for index in 0..graph.vertices.len() {
            assert_eq!(transported[color][transported[color][index]], index);
            assert_eq!(odd_component[color][odd_component[color][index]], index);
            assert_eq!(
                tableau_bender_knuth[color][tableau_bender_knuth[color][index]],
                index
            );
        }
    }
    for (color, transported_map) in transported.iter().enumerate() {
        let mut local_outcomes: BTreeMap<LocalSignature, LocalOutcome> = BTreeMap::new();
        for (index, vertex) in graph.vertices.iter().enumerate() {
            let reflected = graph.vertices[transported_map[index]].coloring.clone();
            let changed_vertices: Vec<usize> = (0..poset.n())
                .filter(|&v| vertex.coloring[v] != reflected[v])
                .collect();
            let witness = MoveWitness {
                code: poset.code(),
                alphabet,
                color,
                source: vertex.coloring.clone(),
                target: reflected.clone(),
                changed_vertices: changed_vertices.clone(),
            };
            if changed_vertices.len() > 1 && study.first_multiple_change.is_none() {
                study.first_multiple_change = Some(witness.clone());
            }
            if changed_vertices.iter().any(|&v| {
                ![color, color + 1].contains(&vertex.coloring[v])
                    || ![color, color + 1].contains(&reflected[v])
            }) && study.first_outside_pair_change.is_none()
            {
                study.first_outside_pair_change = Some(witness);
            }

            let local_restriction = two_color_restriction(&vertex.coloring, color);
            let key = (
                shape(&vertex.coloring, alphabet),
                asc(poset, &vertex.coloring),
                local_restriction.clone(),
            );
            if let Some((first_source, first_target)) = local_outcomes.get(&key) {
                let first_local_target = first_target
                    .as_ref()
                    .map(|value| two_color_restriction(value, color));
                let reflected_local_target = two_color_restriction(&reflected, color);
                if first_local_target.as_ref() != Some(&reflected_local_target)
                    && study.first_context_dependence.is_none()
                {
                    study.first_context_dependence = Some(ContextWitness {
                        code: poset.code(),
                        alphabet,
                        color,
                        weight: key.0.clone(),
                        asc: key.1,
                        local_restriction,
                        first_source: first_source.clone(),
                        first_target: first_target.clone(),
                        second_source: vertex.coloring.clone(),
                        second_target: Some(reflected.clone()),
                    });
                }
            } else {
                local_outcomes.insert(key, (vertex.coloring.clone(), Some(reflected)));
            }
        }
    }
    for left_color in 0..roots {
        for right_color in left_color + 2..roots {
            for index in 0..graph.vertices.len() {
                study.transported_commutation_tests += 1;
                assert_eq!(
                    apply_reflection_word(&transported, index, &[left_color, right_color]),
                    apply_reflection_word(&transported, index, &[right_color, left_color])
                );
            }
        }
    }
    for color in 0..roots.saturating_sub(1) {
        for (index, vertex) in graph.vertices.iter().enumerate() {
            let left_word = [color, color + 1, color];
            let right_word = [color + 1, color, color + 1];
            study.transported_braid_tests += 1;
            assert_eq!(
                apply_reflection_word(&transported, index, &left_word),
                apply_reflection_word(&transported, index, &right_word)
            );

            study.odd_component_braid_tests += 1;
            let left = apply_reflection_word(&odd_component, index, &left_word);
            let right = apply_reflection_word(&odd_component, index, &right_word);
            if left != right {
                study.odd_component_braid_failures += 1;
                if study.first_odd_component_braid_failure.is_none() {
                    study.first_odd_component_braid_failure = Some(BraidFailure {
                        code: poset.code(),
                        alphabet,
                        color,
                        source: vertex.coloring.clone(),
                        left: graph.vertices[left].coloring.clone(),
                        right: graph.vertices[right].coloring.clone(),
                    });
                }
            }

            let bender_left = apply_reflection_word(&tableau_bender_knuth, index, &left_word);
            let bender_right = apply_reflection_word(&tableau_bender_knuth, index, &right_word);
            if bender_left != bender_right {
                study.bender_knuth_braid_failures += 1;
                if study.first_bender_knuth_braid_failure.is_none() {
                    study.first_bender_knuth_braid_failure = Some(BraidFailure {
                        code: poset.code(),
                        alphabet,
                        color,
                        source: vertex.coloring.clone(),
                        left: graph.vertices[bender_left].coloring.clone(),
                        right: graph.vertices[bender_right].coloring.clone(),
                    });
                }
            }
        }
    }
    study
}

fn study_reflections(max_n: usize) -> ReflectionStudy {
    let mut study = ReflectionStudy::default();
    for n in 1..=max_n {
        for poset in natural_unit_interval_orders(n) {
            study.absorb(study_reflections_for_poset(&poset, n));
        }
    }
    study
}

fn print_reflection_study(study: &ReflectionStudy) {
    println!(
        "crystal reflections: {}/{} agree with odd-component switches; {}/{} agree with tableau Bender-Knuth; braid tests={}, distant-commutation tests={}",
        study.matches_odd_component_switch,
        study.comparisons,
        study.bender_knuth_matches,
        study.bender_knuth_comparisons,
        study.transported_braid_tests,
        study.transported_commutation_tests
    );
    if let Some(witness) = &study.first_difference {
        println!(
            "first reflection/switch difference for s_{}: P={:?}, k={}, source={:?}, transported={:?}, odd-component={:?}",
            witness.color + 1,
            witness.code,
            witness.alphabet,
            witness.source,
            witness.transported,
            witness.odd_component_switch
        );
    }
    if let Some(witness) = &study.first_crystal_bender_knuth_difference {
        println!(
            "first crystal-reflection/Bender--Knuth difference for index {}: P={:?}, k={}, source={:?}, reflection={:?}, Bender--Knuth={:?}",
            witness.color + 1,
            witness.code,
            witness.alphabet,
            witness.source,
            witness.transported,
            witness.odd_component_switch
        );
    }
    println!(
        "transported tableau Bender--Knuth agrees with odd-component switch in {}/{} cases",
        study.bender_knuth_switch_matches, study.comparisons
    );
    if let Some(witness) = &study.first_bender_knuth_switch_difference {
        println!(
            "first transported-Bender--Knuth/switch difference for t_{}: P={:?}, k={}, source={:?}, transported={:?}, odd-component={:?}",
            witness.color + 1,
            witness.code,
            witness.alphabet,
            witness.source,
            witness.transported,
            witness.odd_component_switch
        );
    }
    println!(
        "odd-component braid failures: {}/{}",
        study.odd_component_braid_failures, study.odd_component_braid_tests
    );
    if let Some(witness) = &study.first_odd_component_braid_failure {
        println!(
            "first odd-component braid failure for s_{},s_{}: P={:?}, k={}, source={:?}, left={:?}, right={:?}",
            witness.color + 1,
            witness.color + 2,
            witness.code,
            witness.alphabet,
            witness.source,
            witness.left,
            witness.right
        );
    }
    println!(
        "transported Bender--Knuth braid failures: {}/{}",
        study.bender_knuth_braid_failures, study.odd_component_braid_tests
    );
    if let Some(witness) = &study.first_bender_knuth_braid_failure {
        println!(
            "first Bender--Knuth braid failure for s_{},s_{}: P={:?}, k={}, source={:?}, left={:?}, right={:?}",
            witness.color + 1,
            witness.color + 2,
            witness.code,
            witness.alphabet,
            witness.source,
            witness.left,
            witness.right
        );
    }
    if let Some(witness) = &study.first_multiple_change {
        println!(
            "first multi-vertex crystal reflection s_{}: P={:?}, k={}, {:?} -> {:?}, changed={:?}",
            witness.color + 1,
            witness.code,
            witness.alphabet,
            witness.source,
            witness.target,
            witness.changed_vertices
        );
    }
    if let Some(witness) = &study.first_outside_pair_change {
        println!(
            "first crystal reflection touching a color outside pair {}: P={:?}, k={}, {:?} -> {:?}, changed={:?}",
            witness.color + 1,
            witness.code,
            witness.alphabet,
            witness.source,
            witness.target,
            witness.changed_vertices
        );
    }
    if let Some(witness) = &study.first_context_dependence {
        println!(
            "first crystal-reflection two-color-context obstruction for s_{}: P={:?}, k={}, wt={:?}, asc={}, restriction={:?}; {:?} -> {:?}, but {:?} -> {:?}",
            witness.color + 1,
            witness.code,
            witness.alphabet,
            witness.weight,
            witness.asc,
            witness.local_restriction,
            witness.first_source,
            witness.first_target,
            witness.second_source,
            witness.second_target
        );
    }
}

fn two_color_components(poset: &Poset, coloring: &[usize], color: usize) -> Vec<Vec<usize>> {
    let eligible: BTreeSet<usize> = (0..poset.n())
        .filter(|&vertex| coloring[vertex] == color || coloring[vertex] == color + 1)
        .collect();
    let mut unseen = eligible.clone();
    let mut components = Vec::new();
    while let Some(&start) = unseen.first() {
        unseen.remove(&start);
        let mut stack = vec![start];
        let mut component = vec![start];
        while let Some(vertex) = stack.pop() {
            let neighbors: Vec<usize> = unseen
                .iter()
                .copied()
                .filter(|&other| poset.edge(vertex, other))
                .collect();
            for other in neighbors {
                unseen.remove(&other);
                stack.push(other);
                component.push(other);
            }
        }
        component.sort_unstable();
        components.push(component);
    }
    components
}

fn component_signature_reflection(
    poset: &Poset,
    coloring: &[usize],
    color: usize,
    reverse_components: bool,
    cancel_plus_minus: bool,
) -> Vec<usize> {
    let components = two_color_components(poset, coloring, color);
    let mut odd_components: Vec<(usize, bool)> = components
        .iter()
        .enumerate()
        .filter_map(|(index, component)| {
            let smaller = component
                .iter()
                .filter(|&&vertex| coloring[vertex] == color)
                .count();
            let larger = component.len() - smaller;
            assert!(smaller.abs_diff(larger) <= 1);
            (smaller != larger).then_some((index, smaller > larger))
        })
        .collect();
    if reverse_components {
        odd_components.reverse();
    }

    let opener_is_plus = cancel_plus_minus;
    let mut open = Vec::new();
    let mut unmatched_closers = Vec::new();
    for &(component, is_plus) in &odd_components {
        if is_plus == opener_is_plus {
            open.push(component);
        } else if open.pop().is_none() {
            unmatched_closers.push(component);
        }
    }
    let (unmatched_plus, unmatched_minus) = if opener_is_plus {
        (open, unmatched_closers)
    } else {
        (unmatched_closers, open)
    };
    let to_flip: Vec<usize> = if unmatched_plus.len() > unmatched_minus.len() {
        let excess = unmatched_plus.len() - unmatched_minus.len();
        if cancel_plus_minus {
            unmatched_plus.into_iter().take(excess).collect()
        } else {
            unmatched_plus.into_iter().rev().take(excess).collect()
        }
    } else {
        let excess = unmatched_minus.len() - unmatched_plus.len();
        if cancel_plus_minus {
            unmatched_minus.into_iter().rev().take(excess).collect()
        } else {
            unmatched_minus.into_iter().take(excess).collect()
        }
    };
    let mut result = coloring.to_vec();
    for component in to_flip {
        for &vertex in &components[component] {
            result[vertex] = if result[vertex] == color {
                color + 1
            } else {
                color
            };
        }
    }
    result
}

#[derive(Clone, Debug)]
struct CorrectionWitness {
    code: Vec<usize>,
    alphabet: usize,
    color: usize,
    source: Vec<usize>,
    target: Vec<usize>,
    source_lambda: Vec<usize>,
    target_lambda: Vec<usize>,
    source_t: Vec<usize>,
    target_t: Vec<usize>,
}

#[derive(Default)]
struct CorrectionStudy {
    coordinate_states: usize,
    coordinate_collision_excess: usize,
    coordinate_max_fiber: usize,
    states: usize,
    fixed_states: usize,
    same_shape_states: usize,
    same_insertion_states: usize,
    nontrivial_same_inverse_kostka_word: usize,
    nontrivial_same_nonempty_inverse_kostka_word: usize,
    nontrivial_same_insertion_and_inverse_kostka_word: usize,
    trace_classes: [usize; 8],
    nontrivial_trace_classes: [usize; 8],
    cycles_by_length: BTreeMap<usize, usize>,
    first_nontrivial: Option<CorrectionWitness>,
    first_shape_change: Option<CorrectionWitness>,
    first_insertion_change: Option<CorrectionWitness>,
    first_outside_pair_change: Option<CorrectionWitness>,
    first_without_inverse_kostka: Option<CorrectionWitness>,
}

impl CorrectionStudy {
    fn absorb(&mut self, other: Self) {
        self.coordinate_states += other.coordinate_states;
        self.coordinate_collision_excess += other.coordinate_collision_excess;
        self.coordinate_max_fiber = self.coordinate_max_fiber.max(other.coordinate_max_fiber);
        self.states += other.states;
        self.fixed_states += other.fixed_states;
        self.same_shape_states += other.same_shape_states;
        self.same_insertion_states += other.same_insertion_states;
        self.nontrivial_same_inverse_kostka_word += other.nontrivial_same_inverse_kostka_word;
        self.nontrivial_same_nonempty_inverse_kostka_word +=
            other.nontrivial_same_nonempty_inverse_kostka_word;
        self.nontrivial_same_insertion_and_inverse_kostka_word +=
            other.nontrivial_same_insertion_and_inverse_kostka_word;
        for class in 0..8 {
            self.trace_classes[class] += other.trace_classes[class];
            self.nontrivial_trace_classes[class] += other.nontrivial_trace_classes[class];
        }
        for (length, count) in other.cycles_by_length {
            *self.cycles_by_length.entry(length).or_default() += count;
        }
        if self.first_nontrivial.is_none() {
            self.first_nontrivial = other.first_nontrivial;
        }
        if self.first_shape_change.is_none() {
            self.first_shape_change = other.first_shape_change;
        }
        if self.first_insertion_change.is_none() {
            self.first_insertion_change = other.first_insertion_change;
        }
        if self.first_outside_pair_change.is_none() {
            self.first_outside_pair_change = other.first_outside_pair_change;
        }
        if self.first_without_inverse_kostka.is_none() {
            self.first_without_inverse_kostka = other.first_without_inverse_kostka;
        }
    }
}

fn correction_witness(
    poset: &Poset,
    alphabet: usize,
    color: usize,
    graph: &ColoringCrystalGraph,
    source: usize,
    target: usize,
) -> CorrectionWitness {
    CorrectionWitness {
        code: poset.code(),
        alphabet,
        color,
        source: graph.vertices[source].coloring.clone(),
        target: graph.vertices[target].coloring.clone(),
        source_lambda: graph.vertices[source].image.lambda.clone(),
        target_lambda: graph.vertices[target].image.lambda.clone(),
        source_t: graph.vertices[source].image.t.clone(),
        target_t: graph.vertices[target].image.t.clone(),
    }
}

fn study_corrections_for_poset(poset: &Poset, alphabet: usize) -> CorrectionStudy {
    let graph = coloring_crystal_graph(poset, alphabet);
    let indices: BTreeMap<Vec<usize>, usize> = graph
        .vertices
        .iter()
        .enumerate()
        .map(|(index, vertex)| (vertex.coloring.clone(), index))
        .collect();
    let roots = alphabet.saturating_sub(1);
    let mut study = CorrectionStudy::default();
    let mut coordinate_fibers: BTreeMap<TraceCoordinate, usize> = BTreeMap::new();
    for vertex in &graph.vertices {
        *coordinate_fibers
            .entry((
                shape(&vertex.coloring, alphabet),
                vertex.image.t.clone(),
                vertex.inverse_kostka_word.clone(),
            ))
            .or_default() += 1;
    }
    study.coordinate_states = graph.vertices.len();
    study.coordinate_collision_excess = coordinate_fibers
        .values()
        .map(|&size| size.saturating_sub(1))
        .sum();
    study.coordinate_max_fiber = coordinate_fibers.values().copied().max().unwrap_or(0);
    for color in 0..roots {
        let mut transported = vec![0; graph.vertices.len()];
        let mut signature = vec![0; graph.vertices.len()];
        for (index, vertex) in graph.vertices.iter().enumerate() {
            let reflected_target = crystal_reflection_on_target(&vertex.image, alphabet, color);
            let reflected_weight = shape(&reflected_target.q, alphabet);
            let reflected = reverse(poset, &reflected_target, &reflected_weight);
            transported[index] = *indices
                .get(&reflected)
                .expect("a transported reflection must remain in the graph");

            let local = component_signature_reflection(poset, &vertex.coloring, color, false, true);
            signature[index] = *indices
                .get(&local)
                .expect("a signature reflection must remain in the graph");
        }
        let correction: Vec<usize> = (0..graph.vertices.len())
            .map(|index| transported[signature[index]])
            .collect();
        let inverse_correction: Vec<usize> = (0..graph.vertices.len())
            .map(|index| signature[transported[index]])
            .collect();
        for index in 0..graph.vertices.len() {
            assert_eq!(correction[inverse_correction[index]], index);
            assert_eq!(inverse_correction[correction[index]], index);
            assert_eq!(
                signature[correction[signature[index]]],
                inverse_correction[index]
            );

            let target = correction[index];
            let source_vertex = &graph.vertices[index];
            let target_vertex = &graph.vertices[target];
            let signature_vertex = &graph.vertices[signature[index]];
            for vertex in [source_vertex, signature_vertex, target_vertex] {
                let sorted_weight = decreasing_rearrangement(&shape(&vertex.coloring, alphabet));
                assert_eq!(
                    vertex.has_inverse_kostka_step,
                    vertex.image.lambda != sorted_weight
                );
            }
            // Since C_i = S_i R_i and S_i preserves the insertion tableau,
            // C_i(x) and R_i(x) lie in the same transported crystal component.
            assert_eq!(target_vertex.image.lambda, signature_vertex.image.lambda);
            assert_eq!(target_vertex.image.t, signature_vertex.image.t);
            assert_eq!(
                shape(&source_vertex.coloring, alphabet),
                shape(&target_vertex.coloring, alphabet)
            );
            assert_eq!(
                asc(poset, &source_vertex.coloring),
                asc(poset, &target_vertex.coloring)
            );
            let weight = shape(&source_vertex.coloring, alphabet);
            if weight[color] == weight[color + 1] {
                assert_eq!(target, index);
            }

            study.states += 1;
            study.fixed_states += usize::from(target == index);
            let trace_class = usize::from(source_vertex.has_inverse_kostka_step)
                + 2 * usize::from(signature_vertex.has_inverse_kostka_step)
                + 4 * usize::from(target_vertex.has_inverse_kostka_step);
            study.trace_classes[trace_class] += 1;
            study.nontrivial_trace_classes[trace_class] += usize::from(target != index);
            let same_shape = source_vertex.image.lambda == target_vertex.image.lambda;
            let same_insertion = same_shape && source_vertex.image.t == target_vertex.image.t;
            let same_inverse_kostka_word =
                source_vertex.inverse_kostka_word == target_vertex.inverse_kostka_word;
            study.same_shape_states += usize::from(same_shape);
            study.same_insertion_states += usize::from(same_insertion);
            study.nontrivial_same_inverse_kostka_word +=
                usize::from(target != index && same_inverse_kostka_word);
            study.nontrivial_same_nonempty_inverse_kostka_word += usize::from(
                target != index
                    && same_inverse_kostka_word
                    && !source_vertex.inverse_kostka_word.is_empty(),
            );
            study.nontrivial_same_insertion_and_inverse_kostka_word +=
                usize::from(target != index && same_insertion && same_inverse_kostka_word);
            let witness = correction_witness(poset, alphabet, color, &graph, index, target);
            if target != index && study.first_nontrivial.is_none() {
                study.first_nontrivial = Some(witness.clone());
            }
            if target != index && trace_class == 0 && study.first_without_inverse_kostka.is_none() {
                study.first_without_inverse_kostka = Some(witness.clone());
            }
            if !same_shape && study.first_shape_change.is_none() {
                study.first_shape_change = Some(witness.clone());
            }
            if !same_insertion && study.first_insertion_change.is_none() {
                study.first_insertion_change = Some(witness.clone());
            }
            if (0..poset.n()).any(|vertex| {
                source_vertex.coloring[vertex] != target_vertex.coloring[vertex]
                    && (![color, color + 1].contains(&source_vertex.coloring[vertex])
                        || ![color, color + 1].contains(&target_vertex.coloring[vertex]))
            }) && study.first_outside_pair_change.is_none()
            {
                study.first_outside_pair_change = Some(witness);
            }
        }

        let mut seen = vec![false; graph.vertices.len()];
        for start in 0..graph.vertices.len() {
            if seen[start] {
                continue;
            }
            let mut length = 0;
            let mut current = start;
            loop {
                assert!(!seen[current] || current == start);
                if seen[current] {
                    break;
                }
                seen[current] = true;
                length += 1;
                current = correction[current];
            }
            assert_eq!(current, start);
            *study.cycles_by_length.entry(length).or_default() += 1;
        }
    }
    study
}

fn study_corrections(max_n: usize) -> CorrectionStudy {
    let mut study = CorrectionStudy::default();
    for n in 1..=max_n {
        for poset in natural_unit_interval_orders(n) {
            study.absorb(study_corrections_for_poset(&poset, n));
        }
    }
    study
}

fn print_correction_witness(label: &str, witness: &CorrectionWitness) {
    println!(
        "{label} for index {}: P={:?}, k={}, {:?} -> {:?}, shape {:?}->{:?}, T {:?}->{:?}",
        witness.color + 1,
        witness.code,
        witness.alphabet,
        witness.source,
        witness.target,
        witness.source_lambda,
        witness.target_lambda,
        witness.source_t,
        witness.target_t
    );
}

fn print_correction_study(study: &CorrectionStudy) {
    println!(
        "coordinates (weight,T,detailed IK word): states={}, collision excess={}, max fiber={}",
        study.coordinate_states, study.coordinate_collision_excess, study.coordinate_max_fiber
    );
    println!(
        "reflection correction C=S R: fixed={}/{}, same shape={}, same insertion={}, cycles={:?}",
        study.fixed_states,
        study.states,
        study.same_shape_states,
        study.same_insertion_states,
        study.cycles_by_length
    );
    println!(
        "correction by IK trace mask [source, R-source, C-target bits]: totals={:?}, nontrivial={:?}",
        study.trace_classes, study.nontrivial_trace_classes
    );
    println!(
        "nontrivial corrections preserving detailed IK word: {} (nonempty {}), preserving both insertion T and IK word: {}",
        study.nontrivial_same_inverse_kostka_word,
        study.nontrivial_same_nonempty_inverse_kostka_word,
        study.nontrivial_same_insertion_and_inverse_kostka_word
    );
    if let Some(witness) = &study.first_nontrivial {
        print_correction_witness("first nontrivial correction", witness);
    }
    if let Some(witness) = &study.first_shape_change {
        print_correction_witness("first shape-changing correction", witness);
    }
    if let Some(witness) = &study.first_insertion_change {
        print_correction_witness("first insertion-changing correction", witness);
    }
    if let Some(witness) = &study.first_outside_pair_change {
        print_correction_witness("first correction touching an outside color", witness);
    }
    if let Some(witness) = &study.first_without_inverse_kostka {
        print_correction_witness("first nontrivial correction with no IK trace", witness);
    }
}

#[derive(Default)]
struct SignatureReflectionVariant {
    tests: usize,
    braid_tests: usize,
    braid_failures: usize,
    critical_content_tests: usize,
    critical_content_failures: usize,
    first_braid_failure: Option<BraidFailure>,
}

fn study_component_signature_variant(
    max_n: usize,
    reverse_components: bool,
    cancel_plus_minus: bool,
) -> SignatureReflectionVariant {
    let mut study = SignatureReflectionVariant::default();
    for n in 1..=max_n {
        for poset in natural_unit_interval_orders(n) {
            let alphabet = usize::min(n, 3);
            let colorings = proper_colorings(&poset, alphabet);
            let indices: BTreeMap<Vec<usize>, usize> = colorings
                .iter()
                .cloned()
                .enumerate()
                .map(|(index, coloring)| (coloring, index))
                .collect();
            let roots = alphabet.saturating_sub(1);
            let mut maps = vec![vec![0; colorings.len()]; roots];
            for (color, map) in maps.iter_mut().enumerate() {
                for (index, coloring) in colorings.iter().enumerate() {
                    let reflected = component_signature_reflection(
                        &poset,
                        coloring,
                        color,
                        reverse_components,
                        cancel_plus_minus,
                    );
                    assert!(is_proper_coloring(&poset, &reflected));
                    assert_eq!(asc(&poset, &reflected), asc(&poset, coloring));
                    let mut expected_weight = shape(coloring, alphabet);
                    expected_weight.swap(color, color + 1);
                    assert_eq!(shape(&reflected, alphabet), expected_weight);
                    map[index] = *indices
                        .get(&reflected)
                        .expect("a component-signature reflection must stay in the graph");
                    study.tests += 1;
                }
            }
            for map in &maps {
                for index in 0..colorings.len() {
                    assert_eq!(map[map[index]], index);
                }
            }
            for color in 0..roots.saturating_sub(1) {
                for (index, source) in colorings.iter().enumerate() {
                    let left_word = [color, color + 1, color];
                    let right_word = [color + 1, color, color + 1];
                    let left = apply_reflection_word(&maps, index, &left_word);
                    let right = apply_reflection_word(&maps, index, &right_word);
                    study.braid_tests += 1;
                    let critical_content = shape(source, alphabet) == [3, 2, 1];
                    study.critical_content_tests += usize::from(critical_content);
                    if left != right {
                        study.braid_failures += 1;
                        study.critical_content_failures += usize::from(critical_content);
                        if study.first_braid_failure.is_none() {
                            study.first_braid_failure = Some(BraidFailure {
                                code: poset.code(),
                                alphabet,
                                color,
                                source: source.clone(),
                                left: colorings[left].clone(),
                                right: colorings[right].clone(),
                            });
                        }
                    }
                }
            }
        }
    }
    study
}

fn print_component_signature_studies(max_n: usize) {
    for reverse_components in [false, true] {
        for cancel_plus_minus in [false, true] {
            let study =
                study_component_signature_variant(max_n, reverse_components, cancel_plus_minus);
            println!(
                "component-signature reflection (order={}, cancel={}): tests={}, braid failures={}/{}, content (3,2,1) failures={}/{}",
                if reverse_components { "decreasing" } else { "increasing" },
                if cancel_plus_minus { "+-" } else { "-+" },
                study.tests,
                study.braid_failures,
                study.braid_tests,
                study.critical_content_failures,
                study.critical_content_tests
            );
            if let Some(witness) = study.first_braid_failure {
                println!(
                    "  first failure for indices {},{}: P={:?}, k={}, source={:?}, left={:?}, right={:?}",
                    witness.color + 1,
                    witness.color + 2,
                    witness.code,
                    witness.alphabet,
                    witness.source,
                    witness.left,
                    witness.right
                );
            }
        }
    }
}

fn standardize_coloring(coloring: &[usize], decreasing_ties: bool) -> Vec<usize> {
    let alphabet = 1 + *coloring.iter().max().expect("a coloring is nonempty");
    let mut standardized = vec![0; coloring.len()];
    let mut next_label = 0;
    for color in 0..alphabet {
        let mut vertices: Vec<usize> = coloring
            .iter()
            .enumerate()
            .filter_map(|(vertex, &entry)| (entry == color).then_some(vertex))
            .collect();
        if decreasing_ties {
            vertices.reverse();
        }
        for vertex in vertices {
            standardized[vertex] = next_label;
            next_label += 1;
        }
    }
    standardized
}

fn standardize_tableau_entries(entries: &[usize]) -> Vec<usize> {
    let alphabet = 1 + *entries.iter().max().expect("a tableau is nonempty");
    let mut standardized = vec![0; entries.len()];
    let mut next_label = 0;
    for color in 0..alphabet {
        for (position, &entry) in entries.iter().enumerate() {
            if entry == color {
                standardized[position] = next_label;
                next_label += 1;
            }
        }
    }
    standardized
}

#[derive(Clone, Debug)]
struct StandardizationFailure {
    code: Vec<usize>,
    source: Vec<usize>,
    standardized_source: Vec<usize>,
    image: Target,
    standardized_image: Target,
    expected_q: Vec<usize>,
}

fn first_standardization_failure(
    max_n: usize,
    decreasing_ties: bool,
) -> Option<StandardizationFailure> {
    for n in 1..=max_n {
        for poset in natural_unit_interval_orders(n) {
            for source in packed_proper_colorings(&poset) {
                let image = forward(&poset, &source).0;
                let standardized_source = standardize_coloring(&source, decreasing_ties);
                let standardized_image = forward_with_alphabet(&poset, &standardized_source, n).0;
                let expected_q = standardize_tableau_entries(&image.q);
                if standardized_image.lambda != image.lambda
                    || standardized_image.t != image.t
                    || standardized_image.q != expected_q
                {
                    return Some(StandardizationFailure {
                        code: poset.code(),
                        source,
                        standardized_source,
                        image,
                        standardized_image,
                        expected_q,
                    });
                }
            }
        }
    }
    None
}

fn print_standardization_result(
    max_n: usize,
    decreasing_ties: bool,
    failure: Option<&StandardizationFailure>,
) {
    let convention = if decreasing_ties {
        "decreasing"
    } else {
        "increasing"
    };
    if let Some(failure) = failure {
        println!(
            "{convention}-tie standardization fails first at P={:?}, source={:?}, standardized={:?}: image={:?}, standardized image={:?}, expected standardized Q={:?}",
            failure.code,
            failure.source,
            failure.standardized_source,
            failure.image,
            failure.standardized_image,
            failure.expected_q
        );
    } else {
        println!("{convention}-tie standardization is compatible through n={max_n}");
    }
}

#[derive(Default)]
struct CrystalSummary {
    states: usize,
    f_edges: usize,
    string_checks: usize,
    highest_weight_states: usize,
}

impl CrystalSummary {
    fn absorb(&mut self, other: Self) {
        self.states += other.states;
        self.f_edges += other.f_edges;
        self.string_checks += other.string_checks;
        self.highest_weight_states += other.highest_weight_states;
    }
}

fn verify_transported_crystal(
    poset: &Poset,
    source: &[usize],
    target: &Target,
    alphabet: usize,
) -> CrystalSummary {
    let mut summary = CrystalSummary {
        states: 1,
        ..CrystalSummary::default()
    };
    let weight = shape(&target.q, alphabet);
    let mut highest_weight = true;
    for color in 0..alphabet.saturating_sub(1) {
        let epsilon = target_string_length(target, color, true);
        let phi = target_string_length(target, color, false);
        assert_eq!(
            phi as isize - epsilon as isize,
            weight[color] as isize - weight[color + 1] as isize
        );
        summary.string_checks += 1;
        for raising in [false, true] {
            let moved_target = crystal_on_target(target, color, raising);
            if poset.n() <= 3 {
                let moved_by_api = if raising {
                    coloring_e(poset, source, alphabet, color)
                } else {
                    coloring_f(poset, source, alphabet, color)
                };
                let expected = moved_target.as_ref().map(|image| {
                    let moved_mu = shape(&image.q, alphabet);
                    reverse(poset, image, &moved_mu)
                });
                assert_eq!(moved_by_api, expected);
            }
            let Some(moved_target) = moved_target else {
                continue;
            };
            if raising {
                highest_weight = false;
            } else {
                summary.f_edges += 1;
            }
            let moved_mu = shape(&moved_target.q, alphabet);
            let mut expected_mu = shape(&target.q, alphabet);
            if raising {
                expected_mu[color] += 1;
                expected_mu[color + 1] -= 1;
            } else {
                expected_mu[color] -= 1;
                expected_mu[color + 1] += 1;
            }
            assert_eq!(moved_mu, expected_mu);
            let moved_source = reverse(poset, &moved_target, &moved_mu);
            assert!(is_proper_coloring(poset, &moved_source));
            assert_eq!(asc(poset, &moved_source), asc(poset, source));
            assert_eq!(
                forward_with_alphabet(poset, &moved_source, alphabet).0,
                moved_target
            );
            assert_eq!(
                crystal_on_target(&moved_target, color, !raising),
                Some(target.clone())
            );
        }
    }
    if highest_weight {
        assert_eq!(target.q, highest_weight_q(&target.lambda));
        summary.highest_weight_states = 1;
    }
    summary
}

fn trace_checksum(trace: &[TraceEvent]) -> usize {
    trace
        .iter()
        .map(|event| match event {
            TraceEvent::Sw(event) => event.row + event.col + event.normalize_swaps.len(),
            TraceEvent::InverseKostka {
                nu,
                from,
                to,
                local,
            } => {
                let local_sum: usize = local
                    .iter()
                    .map(|event| match event {
                        InverseKostkaEvent::Psi {
                            k,
                            source_row,
                            target_row,
                            inserted_row,
                            deleted_row,
                        } => {
                            k + source_row
                                + target_row
                                + usize::from(*inserted_row)
                                + usize::from(*deleted_row)
                        }
                        InverseKostkaEvent::Theta { row, col } => row + col,
                    })
                    .sum();
                nu.iter().sum::<usize>() + from.lambda.len() + to.lambda.len() + local_sum
            }
        })
        .sum()
}

fn verify_lgv_obstruction() {
    // For n=2, mu=(1,1), nu=(2), the reverse inverse-Kostka fiber has
    // exactly the following opposite-signed elements.  Any ordinary LGV
    // tail switch preserves lambda, so it cannot pair them.
    let catalog = build_catalog(2, &[2], &[1, 1]);
    assert_eq!(catalog.positive.len(), 1);
    assert_eq!(catalog.negative.len(), 1);
    let positive = &catalog.positive[0];
    let negative = &catalog.negative[0];
    assert_eq!(positive.lambda, vec![2]);
    assert_eq!(positive.pi, vec![0, 1]);
    assert_eq!(negative.lambda, vec![1, 1]);
    assert_eq!(negative.pi, vec![1, 0]);
    assert_ne!(positive.lambda, negative.lambda);

    // The even more literal same-cut attempt also fails on this state.  For
    // the chain P, denormalizing A=[1 2] to alpha=(0,2) gives []/[1 2].
    // SW uses row=0,col=0 and moves only the second entry.  Applying that
    // same suffix cut to Q=[1]/[2] gives []/[2 1], which is neither
    // partition-shaped nor row-weakly increasing.
    let chain = Poset { h: vec![0, 1] };
    let normalized_a = vec![0, 0];
    let raw_a = denormalize(&chain, &normalized_a, &[0, 2]);
    assert_eq!(raw_a, vec![1, 1]);
    let (moved_a, moved_pi, row, col) = raw_sw(&chain, &raw_a, &[1, 0]).unwrap();
    assert_eq!((row, col), (0, 0));
    assert_eq!(moved_pi, vec![0, 1]);
    assert_eq!(moved_a, vec![1, 0]);
}

fn verify_all_tail_q_obstruction() {
    // One-based Hessenberg code m=(1,3,3,4), so G has the single edge {2,3}.
    let poset = Poset {
        h: vec![0, 2, 2, 3],
    };
    // A=[2 4]/[1 3], lambda=nu=(2,2), pi=id.
    let a = vec![1, 0, 1, 0];
    let pi = vec![0, 1, 2, 3];
    let (sw_a, _, row, col) = raw_sw(&poset, &a, &pi).unwrap();
    assert_eq!((row, col), (0, 0));
    // SW leaves the even component {2,3} fixed and moves singleton {4}:
    // [2]/[1 3 4].
    assert_eq!(sw_a, vec![1, 0, 1, 1]);
    assert_eq!(des(&poset, &a), 0);
    assert_eq!(des(&poset, &sw_a), 0);

    // A naive switch of every tail component gives [3]/[1 2 4] and changes q.
    let all_tail = vec![1, 1, 0, 1];
    assert_eq!(des(&poset, &all_tail), 1);
}

fn verify_inverse_kostka_n(n: usize) -> (usize, usize) {
    let mut endpoint_states = 0;
    let mut max_local_events = 0;
    for mu in compositions(n) {
        let mu_plus = decreasing_rearrangement(&mu);
        for nu in partitions(n) {
            let catalog = build_catalog(n, &nu, &mu);
            let triples: Vec<Triple> = catalog
                .positive
                .iter()
                .chain(&catalog.negative)
                .cloned()
                .collect();
            if nu == mu_plus {
                assert_eq!(triples, vec![canonical_fixed_triple(n, &mu)]);
            }
            let fiber: BTreeSet<Triple> = triples.iter().cloned().collect();
            for triple in triples {
                endpoint_states += 1;
                let partner = inverse_kostka_local(&triple, &nu, &mu);
                if nu == mu_plus {
                    assert!(partner.is_none());
                    continue;
                }
                let (partner, events) = partner.expect("off-diagonal fiber has no fixed points");
                assert!(fiber.contains(&partner));
                assert_eq!(permutation_sign(&partner.pi), -permutation_sign(&triple.pi));
                assert_eq!(
                    inverse_kostka_local(&partner, &nu, &mu)
                        .expect("local partner must reverse")
                        .0,
                    triple
                );
                max_local_events = max_local_events.max(events.len());
            }
        }
    }
    (endpoint_states, max_local_events)
}

fn crystal_on_triple(triple: &Triple, color: usize, raising: bool) -> Option<Triple> {
    let target = Target {
        lambda: triple.lambda.clone(),
        t: Vec::new(),
        q: triple.q.clone(),
    };
    let moved = crystal_on_target(&target, color, raising)?;
    Some(Triple {
        lambda: triple.lambda.clone(),
        pi: triple.pi.clone(),
        q: moved.q,
    })
}

fn inverse_kostka_total(triple: &Triple, nu: &[usize], mu: &[usize]) -> Triple {
    inverse_kostka_local(triple, nu, mu).map_or_else(|| triple.clone(), |(partner, _)| partner)
}

#[derive(Default)]
struct InverseKostkaCrystalDefects {
    tests: usize,
    defects: usize,
    definedness_defects: usize,
    value_defects: usize,
}

fn inverse_kostka_crystal_defects_n(n: usize) -> InverseKostkaCrystalDefects {
    let mut summary = InverseKostkaCrystalDefects::default();
    for mu in compositions(n) {
        for nu in partitions(n) {
            let catalog = build_catalog(n, &nu, &mu);
            for triple in catalog.positive.iter().chain(&catalog.negative) {
                for color in 0..mu.len().saturating_sub(1) {
                    summary.tests += 1;
                    let after_inverse = inverse_kostka_total(triple, &nu, &mu);
                    let inverse_then_f = crystal_on_triple(&after_inverse, color, false);
                    let f_then_inverse = crystal_on_triple(triple, color, false).map(|moved| {
                        let moved_mu = shape(&moved.q, mu.len());
                        inverse_kostka_total(&moved, &nu, &moved_mu)
                    });
                    if inverse_then_f != f_then_inverse {
                        summary.defects += 1;
                        if inverse_then_f.is_some() == f_then_inverse.is_some() {
                            summary.value_defects += 1;
                        } else {
                            summary.definedness_defects += 1;
                        }
                    }
                }
            }
        }
    }
    summary
}

#[derive(Default)]
struct Summary {
    posets: usize,
    kp_posets: usize,
    colorings: usize,
    kp_colorings: usize,
    targets: usize,
    max_trace_events: usize,
    trace_checksum: usize,
}

fn verify_n(n: usize) -> Summary {
    let mut summary = Summary::default();
    for poset in natural_unit_interval_orders(n) {
        summary.posets += 1;
        let kp_eligible = is_kim_pylyavskyy_eligible(&poset);
        summary.kp_posets += usize::from(kp_eligible);
        let colorings = packed_proper_colorings(&poset);
        let mut by_weight: BTreeMap<Vec<usize>, Vec<Vec<usize>>> = BTreeMap::new();
        for coloring in colorings {
            let k = 1 + *coloring.iter().max().unwrap();
            by_weight
                .entry(shape(&coloring, k))
                .or_default()
                .push(coloring);
        }
        for (mu, sources) in by_weight {
            let targets = target_fiber(&poset, &mu);
            let source_polynomial: BTreeMap<usize, usize> = {
                let mut polynomial = BTreeMap::new();
                for source in &sources {
                    *polynomial.entry(asc(&poset, source)).or_default() += 1;
                }
                polynomial
            };
            let target_polynomial: BTreeMap<usize, usize> = {
                let mut polynomial = BTreeMap::new();
                for target in &targets {
                    *polynomial.entry(inv_g(&poset, &target.t)).or_default() += 1;
                }
                polynomial
            };
            assert_eq!(
                source_polynomial,
                target_polynomial,
                "q-fiber mismatch for P={:?}, mu={mu:?}",
                poset.code()
            );

            let mut images = BTreeSet::new();
            for source in &sources {
                let (target, trace) = forward(&poset, source);
                assert_eq!(asc(&poset, source), inv_g(&poset, &target.t));
                assert_eq!(reverse(&poset, &target, &mu), *source);
                assert!(images.insert(target));
                let event_count: usize = trace
                    .iter()
                    .map(|event| match event {
                        TraceEvent::Sw(_) => 1,
                        TraceEvent::InverseKostka { local, .. } => local.len(),
                    })
                    .sum();
                summary.max_trace_events = summary.max_trace_events.max(event_count);
                summary.trace_checksum =
                    summary.trace_checksum.wrapping_add(trace_checksum(&trace));
            }
            let expected: BTreeSet<Target> = targets.into_iter().collect();
            assert_eq!(
                images,
                expected,
                "bijection miss for P={:?}, mu={mu:?}",
                poset.code()
            );
            summary.colorings += sources.len();
            if kp_eligible {
                summary.kp_colorings += sources.len();
            }
            summary.targets += expected.len();
        }
    }
    summary
}

fn verify_one_empty_color_n(n: usize) -> CrystalSummary {
    let mut crystal_summary = CrystalSummary::default();
    for poset in natural_unit_interval_orders(n) {
        let mut by_weight: BTreeMap<Vec<usize>, Vec<Vec<usize>>> = BTreeMap::new();
        for coloring in packed_proper_colorings(&poset) {
            let support = 1 + *coloring.iter().max().unwrap();
            for gap in 0..=support {
                let embedded: Vec<usize> = coloring
                    .iter()
                    .map(|&color| color + usize::from(color >= gap))
                    .collect();
                let mu = shape(&embedded, support + 1);
                assert_eq!(mu.iter().filter(|&&part| part == 0).count(), 1);
                by_weight.entry(mu).or_default().push(embedded);
            }
        }
        for (mu, sources) in by_weight {
            let expected: BTreeSet<Target> = target_fiber(&poset, &mu).into_iter().collect();
            let mut images = BTreeSet::new();
            for source in sources {
                let (target, _) = forward_with_alphabet(&poset, &source, mu.len());
                assert_eq!(shape(&target.q, mu.len()), mu);
                assert_eq!(asc(&poset, &source), inv_g(&poset, &target.t));
                assert_eq!(reverse(&poset, &target, &mu), source);
                crystal_summary.absorb(verify_transported_crystal(
                    &poset,
                    &source,
                    &target,
                    mu.len(),
                ));
                assert!(images.insert(target));
            }
            assert_eq!(images, expected);
        }
    }
    crystal_summary
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.get(1).map(String::as_str) == Some("--dot") {
        assert_eq!(args.len(), 4, "usage: --dot h_1,...,h_n alphabet");
        let code: Vec<usize> = args[2]
            .split(',')
            .map(|part| {
                part.parse::<usize>()
                    .expect("Hessenberg code must be numeric")
            })
            .collect();
        let n = code.len();
        let h: Vec<usize> = code
            .iter()
            .map(|&entry| {
                entry
                    .checked_sub(1)
                    .expect("Hessenberg entries are one-based")
            })
            .collect();
        assert!(
            h.iter()
                .enumerate()
                .all(|(i, &entry)| i <= entry && entry < n)
                && h.windows(2).all(|window| window[0] <= window[1]),
            "invalid natural-unit-interval-order Hessenberg code"
        );
        let alphabet = args[3]
            .parse::<usize>()
            .expect("alphabet size must be numeric");
        print!("{}", crystal_graph_dot(&Poset { h }, alphabet));
        return;
    }
    verify_lgv_obstruction();
    verify_all_tail_q_obstruction();
    println!("LGV obstruction: n=2, mu=(1,1), nu=(2), lambda changes (2) <-> (1,1)");
    println!("all-tail q obstruction: n=4, m=(1,3,3,4), G={{2,3}}, q changes 0 -> 1");
    let locality_study = study_crystal_locality(5);
    print_locality_study(&locality_study);
    let increasing_standardization = first_standardization_failure(5, false);
    let decreasing_standardization = first_standardization_failure(5, true);
    print_standardization_result(5, false, increasing_standardization.as_ref());
    print_standardization_result(5, true, decreasing_standardization.as_ref());
    let reflection_study = study_reflections(5);
    print_reflection_study(&reflection_study);
    let correction_study = study_corrections(5);
    print_correction_study(&correction_study);
    print_component_signature_studies(6);
    let mut total = Summary::default();
    for n in 1..=5 {
        let (inverse_kostka_states, max_local_events) = verify_inverse_kostka_n(n);
        let inverse_kostka_defects = inverse_kostka_crystal_defects_n(n);
        let summary = verify_n(n);
        let crystal = verify_one_empty_color_n(n);
        let mut graph_summary = GraphSummary::default();
        for poset in natural_unit_interval_orders(n) {
            graph_summary.absorb(verify_coloring_crystal_graph(&poset, n));
        }
        println!(
            "n={n}: posets={} (KP {}), packed proper colorings={} (KP {}), one-empty-color maps={}, crystal f-edges={}, string checks={}, highest weights={}, full k=n graph vertices={}, edges={}, components={}, targets={}, inverse-Kostka endpoints={}, IK/F tests={}, defects={} (definedness {}, value {}), max_local_events={}, max_trace_events={}, checksum={}",
            summary.posets,
            summary.kp_posets,
            summary.colorings,
            summary.kp_colorings,
            crystal.states,
            crystal.f_edges,
            crystal.string_checks,
            crystal.highest_weight_states,
            graph_summary.vertices,
            graph_summary.edges,
            graph_summary.components,
            summary.targets,
            inverse_kostka_states,
            inverse_kostka_defects.tests,
            inverse_kostka_defects.defects,
            inverse_kostka_defects.definedness_defects,
            inverse_kostka_defects.value_defects,
            max_local_events,
            summary.max_trace_events,
            summary.trace_checksum
        );
        total.posets += summary.posets;
        total.kp_posets += summary.kp_posets;
        total.colorings += summary.colorings;
        total.kp_colorings += summary.kp_colorings;
        total.targets += summary.targets;
        total.max_trace_events = total.max_trace_events.max(summary.max_trace_events);
        total.trace_checksum = total.trace_checksum.wrapping_add(summary.trace_checksum);
    }
    println!(
        "total: posets={} (KP {}), colorings={} (KP {}), targets={}, max_trace_events={}, checksum={}",
        total.posets,
        total.kp_posets,
        total.colorings,
        total.kp_colorings,
        total.targets,
        total.max_trace_events,
        total.trace_checksum
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn inverse_kostka_lgv_obstruction_is_minimal() {
        verify_lgv_obstruction();
        verify_all_tail_q_obstruction();
        for mu in [vec![1], vec![1, 1], vec![2]] {
            for nu in partitions(mu.iter().sum()) {
                let catalog = build_catalog(mu.iter().sum(), &nu, &mu);
                assert_eq!(
                    catalog.positive.len() as isize - catalog.negative.len() as isize,
                    isize::from(nu == decreasing_rearrangement(&mu))
                );
            }
        }
    }

    #[test]
    fn exhaustive_through_four() {
        for n in 1..=4 {
            verify_inverse_kostka_n(n);
            verify_n(n);
            verify_one_empty_color_n(n);
        }
    }

    #[test]
    fn kim_pylyavskyy_avoidance_class_through_five() {
        let excluded: Vec<Vec<usize>> = natural_unit_interval_orders(5)
            .into_iter()
            .filter(|poset| !is_kim_pylyavskyy_eligible(poset))
            .map(|poset| poset.code())
            .collect();
        assert_eq!(excluded, vec![vec![2, 4, 4, 5, 5]]);
    }

    #[test]
    fn transported_reflections_and_signature_braid_obstruction() {
        fn alternating_ending_in_one(length: usize) -> Vec<usize> {
            (0..length).map(|index| (length - 1 - index) % 2).collect()
        }

        fn path_sheet_word(a: usize, position: usize) -> Vec<usize> {
            let n = 2 * a;
            let mut word = alternating_ending_in_one(position - 1);
            word.push(2);
            word.extend(alternating_ending_in_one(n - position));
            word
        }

        fn path_fiber(a: usize) -> BTreeSet<Vec<usize>> {
            fn recurse(
                n: usize,
                target_asc: usize,
                remaining: &mut [usize; 3],
                word: &mut Vec<usize>,
                current_asc: usize,
                out: &mut BTreeSet<Vec<usize>>,
            ) {
                if word.len() == n {
                    if current_asc == target_asc {
                        out.insert(word.clone());
                    }
                    return;
                }
                for color in 0..3 {
                    if remaining[color] == 0 || word.last() == Some(&color) {
                        continue;
                    }
                    let new_asc =
                        current_asc + usize::from(word.last().is_some_and(|&last| last < color));
                    if new_asc > target_asc {
                        continue;
                    }
                    remaining[color] -= 1;
                    word.push(color);
                    recurse(n, target_asc, remaining, word, new_asc, out);
                    word.pop();
                    remaining[color] += 1;
                }
            }

            let mut out = BTreeSet::new();
            recurse(
                2 * a,
                a - 1,
                &mut [a, a - 1, 1],
                &mut Vec::new(),
                0,
                &mut out,
            );
            out
        }

        let reflection_study = study_reflections(4);
        assert!(reflection_study.transported_braid_tests > 0);

        let poset = Poset {
            h: vec![0, 1, 3, 4, 5, 5],
        };
        let source = vec![0, 1, 0, 2, 1, 0];
        let apply_word = |start: &[usize], word: &[usize]| {
            word.iter().fold(start.to_vec(), |coloring, &color| {
                component_signature_reflection(&poset, &coloring, color, false, true)
            })
        };
        assert_eq!(apply_word(&source, &[0, 1, 0]), vec![0, 2, 2, 1, 2, 1]);
        assert_eq!(apply_word(&source, &[1, 0, 1]), vec![1, 2, 2, 1, 2, 0]);

        let defect_word = [1, 0, 1, 0, 1, 0];
        let first = vec![1, 2, 2, 1, 2, 0];
        let second = vec![0, 2, 2, 1, 2, 1];
        let third = vec![1, 2, 2, 1, 0, 2];
        assert_eq!(apply_word(&first, &defect_word), second);
        assert_eq!(apply_word(&second, &defect_word), third);
        assert_eq!(apply_word(&third, &defect_word), first);

        let fixed_weight = vec![1, 2, 3];
        let weight_fiber: Vec<Vec<usize>> = proper_colorings(&poset, 3)
            .into_iter()
            .filter(|coloring| shape(coloring, 3) == fixed_weight)
            .collect();
        assert_eq!(weight_fiber.len(), 22);
        assert_eq!(
            weight_fiber
                .iter()
                .filter(|coloring| apply_word(coloring, &defect_word) != **coloring)
                .count(),
            3
        );
        assert_eq!(
            weight_fiber
                .iter()
                .filter(|coloring| asc(&poset, coloring) == 1)
                .count(),
            11
        );
        assert_eq!(
            weight_fiber
                .iter()
                .filter(|coloring| asc(&poset, coloring) == 2)
                .count(),
            11
        );

        let mut orbit = BTreeSet::from([source.clone()]);
        let mut frontier = vec![source];
        while let Some(coloring) = frontier.pop() {
            for color in 0..2 {
                let neighbor = apply_word(&coloring, &[color]);
                if orbit.insert(neighbor.clone()) {
                    frontier.push(neighbor);
                }
            }
        }
        assert_eq!(orbit.len(), 18);
        let mut weights = BTreeMap::new();
        for coloring in &orbit {
            assert_eq!(asc(&poset, coloring), 1);
            let neighbors: BTreeSet<Vec<usize>> =
                (0..2).map(|color| apply_word(coloring, &[color])).collect();
            assert_eq!(neighbors.len(), 2);
            assert!(!neighbors.contains(coloring));
            *weights.entry(shape(coloring, 3)).or_insert(0) += 1;
        }
        assert_eq!(weights.len(), 6);
        assert!(weights.values().all(|&multiplicity| multiplicity == 3));

        let component_words = |coloring: &[usize], color: usize| {
            two_color_components(&poset, coloring, color)
                .into_iter()
                .map(|component| {
                    component
                        .into_iter()
                        .map(|vertex| coloring[vertex])
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>()
        };
        let context_x = vec![0, 2, 1, 0, 1, 0];
        let context_y = vec![2, 0, 1, 0, 1, 0];
        assert_eq!(shape(&context_x, 3), vec![3, 2, 1]);
        assert_eq!(shape(&context_y, 3), vec![3, 2, 1]);
        assert_eq!(asc(&poset, &context_x), 1);
        assert_eq!(asc(&poset, &context_y), 1);
        assert_eq!(
            component_words(&context_x, 0),
            component_words(&context_y, 0)
        );
        assert_eq!(
            component_words(&context_x, 1),
            component_words(&context_y, 1)
        );
        assert_eq!(apply_word(&context_x, &defect_word), vec![0, 1, 2, 0, 1, 0]);
        assert_eq!(apply_word(&context_y, &defect_word), context_y);

        let path_poset = Poset {
            h: vec![1, 2, 3, 4, 5, 5],
        };
        let apply_path_word = |start: &[usize], word: &[usize]| {
            word.iter().fold(start.to_vec(), |coloring, &color| {
                component_signature_reflection(&path_poset, &coloring, color, false, true)
            })
        };
        let five_cycle = [
            vec![0, 1, 0, 2, 1, 0],
            vec![0, 2, 1, 0, 1, 0],
            vec![1, 0, 1, 0, 2, 0],
            vec![2, 0, 1, 0, 1, 0],
            vec![1, 0, 2, 0, 1, 0],
        ];
        for index in 0..five_cycle.len() {
            assert_eq!(
                apply_path_word(&five_cycle[index], &defect_word),
                five_cycle[(index + 1) % five_cycle.len()]
            );
        }
        let mut path_orbit = BTreeSet::from([five_cycle[0].clone()]);
        let mut path_frontier = vec![five_cycle[0].clone()];
        while let Some(coloring) = path_frontier.pop() {
            for color in 0..2 {
                let neighbor = apply_path_word(&coloring, &[color]);
                if path_orbit.insert(neighbor.clone()) {
                    path_frontier.push(neighbor);
                }
            }
        }
        assert_eq!(path_orbit.len(), 30);
        let mut path_weights = BTreeMap::new();
        for coloring in path_orbit {
            *path_weights.entry(shape(&coloring, 3)).or_insert(0) += 1;
        }
        assert_eq!(path_weights.len(), 6);
        assert!(path_weights.values().all(|&multiplicity| multiplicity == 5));

        let mut defect_cycles = BTreeMap::new();
        for order in natural_unit_interval_orders(6) {
            let fiber: Vec<Vec<usize>> = proper_colorings(&order, 3)
                .into_iter()
                .filter(|coloring| shape(coloring, 3) == vec![3, 2, 1])
                .collect();
            let fiber_set: BTreeSet<Vec<usize>> = fiber.iter().cloned().collect();
            let mut seen = BTreeSet::new();
            for start in fiber {
                if seen.contains(&start) {
                    continue;
                }
                let mut current = start.clone();
                let mut length = 0;
                loop {
                    assert!(fiber_set.contains(&current));
                    if !seen.insert(current.clone()) {
                        assert_eq!(current, start);
                        break;
                    }
                    length += 1;
                    for &color in &defect_word {
                        current =
                            component_signature_reflection(&order, &current, color, false, true);
                    }
                }
                *defect_cycles.entry(length).or_insert(0) += 1;
            }
        }
        assert_eq!(defect_cycles, BTreeMap::from([(1, 1258), (3, 11), (5, 1)]));

        for a in 3..=10 {
            let n = 2 * a;
            let path = Poset {
                h: (0..n).map(|vertex| (vertex + 1).min(n - 1)).collect(),
            };
            let expected_fiber: BTreeSet<Vec<usize>> = (1..n)
                .map(|position| path_sheet_word(a, position))
                .collect();
            assert_eq!(path_fiber(a), expected_fiber);
            let defect = |coloring: &[usize]| {
                defect_word
                    .iter()
                    .fold(coloring.to_vec(), |current, &color| {
                        component_signature_reflection(&path, &current, color, false, true)
                    })
            };
            for position in 1..n {
                let expected_position = if position == 1 {
                    n - 3
                } else if position == 3 {
                    4
                } else if position >= 5 && position % 2 == 1 {
                    position - 4
                } else if position <= n - 6 && position % 2 == 0 {
                    position + 4
                } else if position == n - 4 {
                    n - 1
                } else {
                    assert_eq!(position, n - 2);
                    2
                };
                assert_eq!(
                    defect(&path_sheet_word(a, position)),
                    path_sheet_word(a, expected_position)
                );
            }
            let mut seen_positions = BTreeSet::new();
            let mut cycle_lengths = Vec::new();
            for start in 1..n {
                if seen_positions.contains(&start) {
                    continue;
                }
                let mut current = path_sheet_word(a, start);
                let mut length = 0;
                loop {
                    let position = (1..n)
                        .find(|&position| path_sheet_word(a, position) == current)
                        .expect("the defect must preserve the path sheet family");
                    if !seen_positions.insert(position) {
                        assert_eq!(position, start);
                        break;
                    }
                    length += 1;
                    current = defect(&current);
                }
                cycle_lengths.push(length);
            }
            cycle_lengths.sort_unstable();
            let mut expected_lengths = if a % 2 == 1 {
                vec![2 * a - 1]
            } else {
                vec![a / 2, a / 2, a - 1]
            };
            expected_lengths.sort_unstable();
            assert_eq!(cycle_lengths, expected_lengths);
        }
    }
}
