use std::collections::{BTreeMap, BTreeSet, HashSet, VecDeque};

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

#[derive(Clone, Debug, Eq, PartialEq)]
struct TableauState {
    lambda: Vec<usize>,
    entries: Vec<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct HookState {
    /// Shape of the special rim-hook tabloid.
    lambda: Vec<usize>,
    /// Its Allen--Celano--Mason permutation, in zero-based one-line notation.
    sigma: Vec<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct LmState {
    /// The adjoint carrier, keyed by the partition content of each tableau.
    carrier: BTreeMap<Vec<usize>, TableauState>,
    b: TableauState,
    c: HookState,
    d: TableauState,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum LoehrMendesEvent {
    AdjointSwap {
        content: Vec<usize>,
        used_carrier: bool,
        parked_old_d: bool,
    },
    Er {
        row: usize,
        largest: usize,
    },
    CarrierSwap {
        content: Vec<usize>,
        used_carrier: bool,
        parked_old_b: bool,
    },
}

#[derive(Clone, Debug)]
enum LoehrMendesTraceEvent {
    Sw(SwEvent),
    InverseKostka {
        nu: Vec<usize>,
        from: Triple,
        to: Triple,
        local: Vec<LoehrMendesEvent>,
    },
}

fn reversed_loehr_mendes_events(events: &[LoehrMendesEvent]) -> Vec<LoehrMendesEvent> {
    events
        .iter()
        .rev()
        .map(|event| match event {
            LoehrMendesEvent::AdjointSwap {
                content,
                used_carrier,
                parked_old_d,
            } => LoehrMendesEvent::AdjointSwap {
                content: content.clone(),
                used_carrier: *parked_old_d,
                parked_old_d: *used_carrier,
            },
            LoehrMendesEvent::Er { row, largest } => LoehrMendesEvent::Er {
                row: *row,
                largest: *largest,
            },
            LoehrMendesEvent::CarrierSwap {
                content,
                used_carrier,
                parked_old_b,
            } => LoehrMendesEvent::CarrierSwap {
                content: content.clone(),
                used_carrier: *parked_old_b,
                parked_old_b: *used_carrier,
            },
        })
        .collect()
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

/// The precise iterated Bender--Knuth word in Loehr--Mendes Section 7.3.
///
/// Starting from the decreasing rearrangement of `composition`, the word
/// places the desired part in each position by their palindromic
/// transposition `BK_{r,j}`.  This is deliberately separate from
/// `normalization_swaps`: different reduced/nonreduced words have the same
/// effect on content but need not have the same effect on a tableau.
fn loehr_mendes_normalization_swaps(composition: &[usize]) -> Vec<usize> {
    let mut counts = composition.to_vec();
    counts.sort_unstable_by(|a, b| b.cmp(a));
    let mut swaps = Vec::new();
    for (position, &target) in composition.iter().enumerate() {
        let source = (position..counts.len())
            .find(|&index| counts[index] == target)
            .expect("target composition must permute its decreasing rearrangement");
        if source == position {
            continue;
        }
        swaps.extend(position..source);
        swaps.extend((position..source - 1).rev());
        counts.swap(position, source);
    }
    assert_eq!(counts, composition);
    swaps
}

fn loehr_mendes_to_composition(
    entries: &[usize],
    lambda: &[usize],
    composition: &[usize],
) -> Vec<usize> {
    let mut result = entries.to_vec();
    for value in loehr_mendes_normalization_swaps(composition) {
        result = bender_knuth(lambda, &result, value);
    }
    result
}

fn loehr_mendes_to_partition(
    entries: &[usize],
    lambda: &[usize],
    composition: &[usize],
) -> Vec<usize> {
    let mut result = entries.to_vec();
    for &value in loehr_mendes_normalization_swaps(composition).iter().rev() {
        result = bender_knuth(lambda, &result, value);
    }
    result
}

fn tableau_content(tableau: &TableauState, alphabet: usize) -> Vec<usize> {
    let mut content = tableau_weak_content(tableau, alphabet);
    while content.last() == Some(&0) {
        content.pop();
    }
    content
}

fn tableau_weak_content(tableau: &TableauState, alphabet: usize) -> Vec<usize> {
    assert!(tableau.entries.iter().all(|&value| value < alphabet));
    let mut content = vec![0; alphabet];
    for &value in &tableau.entries {
        content[value] += 1;
    }
    content
}

fn superstandard_tableau(lambda: &[usize]) -> TableauState {
    TableauState {
        lambda: lambda.to_vec(),
        entries: lambda
            .iter()
            .enumerate()
            .flat_map(|(row, &length)| std::iter::repeat_n(row, length))
            .collect(),
    }
}

fn is_superstandard(tableau: &TableauState) -> bool {
    tableau
        .lambda
        .iter()
        .enumerate()
        .flat_map(|(row, &length)| std::iter::repeat_n(row, length))
        .eq(tableau.entries.iter().copied())
}

fn hook_content(hook: &HookState) -> Vec<usize> {
    decreasing_rearrangement(&hook_terminal_content(hook))
}

fn hook_terminal_content(hook: &HookState) -> Vec<usize> {
    assert_eq!(hook.lambda.len(), hook.sigma.len());
    let delta: Vec<usize> = hook
        .lambda
        .iter()
        .enumerate()
        .map(|(row, &length)| {
            let value = length as isize + hook.sigma[row] as isize - row as isize;
            assert!(value >= 0, "negative special-rim-hook length");
            value as usize
        })
        .collect();
    inverse_permutation(&hook.sigma)
        .into_iter()
        .map(|row| delta[row])
        .collect()
}

fn is_superspecial(hook: &HookState) -> bool {
    hook.sigma
        .iter()
        .enumerate()
        .all(|(row, &value)| row == value)
}

fn partition_strictly_dominates(lambda: &[usize], mu: &[usize]) -> bool {
    let length = lambda.len().max(mu.len());
    let mut lambda_sum = 0;
    let mut mu_sum = 0;
    let mut strict = false;
    for index in 0..length {
        lambda_sum += lambda.get(index).copied().unwrap_or(0);
        mu_sum += mu.get(index).copied().unwrap_or(0);
        if lambda_sum < mu_sum {
            return false;
        }
        strict |= lambda_sum > mu_sum;
    }
    strict && lambda_sum == mu_sum
}

fn assert_loehr_mendes_carrier_chain(state: &LmState, nu: &[usize], n: usize) {
    for (content, tableau) in &state.carrier {
        assert!(!is_superstandard(tableau));
        assert_eq!(*content, tableau_content(tableau, n));
        assert!(partition_strictly_dominates(&tableau.lambda, content));
    }
    let mut shape = nu.to_vec();
    let mut used = BTreeSet::new();
    while shape != state.b.lambda {
        let candidates: Vec<(&Vec<usize>, &TableauState)> = state
            .carrier
            .iter()
            .filter(|(_, tableau)| tableau.lambda == shape)
            .collect();
        assert_eq!(
            candidates.len(),
            1,
            "carrier is not a single dominance chain"
        );
        let (content, _) = candidates[0];
        assert!(
            used.insert(content.clone()),
            "carrier chain contains a cycle"
        );
        shape = content.clone();
    }
    assert_eq!(used.len(), state.carrier.len());
}

fn er_local(
    tableau: &TableauState,
    hook: &HookState,
) -> Option<(TableauState, HookState, LoehrMendesEvent)> {
    let n: usize = tableau.lambda.iter().sum();
    assert_eq!(tableau.entries.len(), n);
    assert_eq!(tableau_content(tableau, n), hook_content(hook));
    if is_superstandard(tableau) && is_superspecial(hook) {
        return None;
    }

    // Loehr--Mendes use the modified Egecioglu--Remmel map: first apply
    // their deterministic iterated Bender--Knuth map from partition content
    // to the terminal-row composition content of the rim-hook tabloid, make
    // the raw ER move, and then normalize the new composition content back to
    // a partition.  Algorithm 3.6 of Allen--Celano--Mason is precisely the
    // middle raw move in the permutation encoding.
    let old_terminal_content = hook_terminal_content(hook);
    let raw_entries =
        loehr_mendes_to_composition(&tableau.entries, &tableau.lambda, &old_terminal_content);
    let raw_tableau = TableauState {
        lambda: tableau.lambda.clone(),
        entries: raw_entries,
    };
    assert_eq!(
        tableau_weak_content(&raw_tableau, hook.sigma.len()),
        old_terminal_content
    );
    let rows = entries_to_rows(&raw_tableau.lambda, &raw_tableau.entries, false);
    let row = rows
        .iter()
        .enumerate()
        .find_map(|(row, entries)| {
            let largest = *entries.last().expect("tableau rows are nonempty");
            (largest != row).then_some(row)
        })
        .expect("Egecioglu--Remmel nonfixed state must have a nonconstant row");
    let largest = *rows[row].last().unwrap();
    assert!(largest > row);
    assert!(largest > 0);
    assert!(largest < hook.sigma.len());

    let offset: usize = tableau.lambda[..row].iter().sum();
    let col = rows[row]
        .iter()
        .position(|&entry| entry == largest)
        .expect("largest row entry must occur");
    let mut changed = raw_tableau.entries.clone();
    changed[offset + col] = largest - 1;
    let transformed_raw = TableauState {
        lambda: raw_tableau.lambda.clone(),
        entries: bender_knuth(&raw_tableau.lambda, &changed, largest - 1),
    };

    let mut sigma = hook.sigma.clone();
    swap_permutation_values(&mut sigma, largest - 1);
    let transformed_hook = HookState {
        lambda: hook.lambda.clone(),
        sigma,
    };
    let new_terminal_content = hook_terminal_content(&transformed_hook);
    assert_eq!(
        tableau_weak_content(&transformed_raw, transformed_hook.sigma.len()),
        new_terminal_content
    );
    let transformed = TableauState {
        lambda: transformed_raw.lambda.clone(),
        entries: loehr_mendes_to_partition(
            &transformed_raw.entries,
            &transformed_raw.lambda,
            &new_terminal_content,
        ),
    };
    assert_eq!(
        tableau_content(&transformed, n),
        hook_content(&transformed_hook)
    );
    assert_eq!(
        permutation_sign(&transformed_hook.sigma),
        -permutation_sign(&hook.sigma)
    );
    Some((
        transformed,
        transformed_hook,
        LoehrMendesEvent::Er { row, largest },
    ))
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

fn triple_to_hook(triple: &Triple) -> HookState {
    let ell = triple.lambda.len();
    assert!(triple
        .pi
        .iter()
        .enumerate()
        .skip(ell)
        .all(|(index, &value)| index == value));
    let short_pi = triple.pi[..ell].to_vec();
    assert!(short_pi.iter().all(|&value| value < ell));
    HookState {
        lambda: triple.lambda.clone(),
        sigma: inverse_permutation(&short_pi),
    }
}

fn hook_to_pi(hook: &HookState, n: usize) -> Vec<usize> {
    let mut pi = inverse_permutation(&hook.sigma);
    pi.extend(hook.lambda.len()..n);
    pi
}

fn inverse_kostka_loehr_mendes_local(
    triple: &Triple,
    nu: &[usize],
    mu: &[usize],
) -> Option<(Triple, Vec<LoehrMendesEvent>)> {
    let n = triple.pi.len();
    let nu_partition = decreasing_rearrangement(nu);
    let mu_partition = decreasing_rearrangement(mu);
    if nu_partition == mu_partition {
        assert_eq!(*triple, canonical_fixed_triple(n, mu));
        return None;
    }

    let normalized_q = normalize_ssyt_content(&triple.q, &triple.lambda, mu);
    let d = TableauState {
        lambda: triple.lambda.clone(),
        entries: normalized_q,
    };
    assert_eq!(tableau_content(&d, n), mu_partition);
    let c = triple_to_hook(triple);
    assert_eq!(hook_content(&c), nu_partition);
    let mut state = LmState {
        carrier: BTreeMap::new(),
        b: superstandard_tableau(&nu_partition),
        c,
        d,
    };
    let input_sign = permutation_sign(&triple.pi);
    let mut events = Vec::new();

    for _ in 0..100_000 {
        assert_loehr_mendes_carrier_chain(&state, &nu_partition, n);
        if is_superstandard(&state.b) && is_superspecial(&state.c) {
            let used_carrier = state.carrier.contains_key(&mu_partition);
            let z = state
                .carrier
                .remove(&mu_partition)
                .unwrap_or_else(|| superstandard_tableau(&mu_partition));
            let old_d = std::mem::replace(&mut state.d, z.clone());
            state.b = superstandard_tableau(&z.lambda);
            state.c = HookState {
                lambda: z.lambda,
                sigma: (0..state.b.lambda.len()).collect(),
            };
            let parked_old_d = !is_superstandard(&old_d);
            if parked_old_d {
                let content = tableau_content(&old_d, n);
                assert_ne!(content, nu_partition);
                assert!(state.carrier.insert(content, old_d).is_none());
            }
            assert_ne!(used_carrier, parked_old_d);
            events.push(LoehrMendesEvent::AdjointSwap {
                content: mu_partition.clone(),
                used_carrier,
                parked_old_d,
            });
        } else {
            let (b, c, event) = er_local(&state.b, &state.c)
                .expect("nonfixed Loehr--Mendes (B,C) pair must move under ER");
            state.b = b;
            state.c = c;
            events.push(event);
        }

        assert_loehr_mendes_carrier_chain(&state, &nu_partition, n);

        if is_superstandard(&state.b) && tableau_content(&state.b, n) == nu_partition {
            assert!(state.carrier.is_empty());
            assert_eq!(hook_content(&state.c), nu_partition);
            assert_eq!(state.c.lambda, state.d.lambda);
            assert_eq!(permutation_sign(&state.c.sigma), -input_sign);
            let q = denormalize_ssyt_content(&state.d.entries, &state.d.lambda, mu);
            let result = Triple {
                lambda: state.c.lambda.clone(),
                pi: hook_to_pi(&state.c, n),
                q,
            };
            assert_eq!(
                decreasing_rearrangement(&alpha(&result.lambda, &result.pi).unwrap()),
                nu_partition
            );
            assert_eq!(permutation_sign(&result.pi), -input_sign);
            return Some((result, events));
        }

        let content = tableau_content(&state.b, n);
        let used_carrier = state.carrier.contains_key(&content);
        let z = state
            .carrier
            .remove(&content)
            .unwrap_or_else(|| superstandard_tableau(&content));
        let old_b = std::mem::replace(&mut state.b, z);
        let parked_old_b = !is_superstandard(&old_b);
        if parked_old_b {
            let old_content = tableau_content(&old_b, n);
            assert_ne!(old_content, nu_partition);
            assert!(state.carrier.insert(old_content, old_b).is_none());
        }
        assert_ne!(used_carrier, parked_old_b);
        events.push(LoehrMendesEvent::CarrierSwap {
            content,
            used_carrier,
            parked_old_b,
        });
        assert_loehr_mendes_carrier_chain(&state, &nu_partition, n);
    }
    panic!("Loehr--Mendes path exceeded safety bound");
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

fn conjugate_partition(lambda: &[usize]) -> Vec<usize> {
    let width = lambda.first().copied().unwrap_or(0);
    (0..width)
        .map(|col| lambda.iter().filter(|&&length| col < length).count())
        .collect()
}

fn p_tableau_column_word(tableau: &[usize]) -> Vec<usize> {
    let row_count = 1 + tableau.iter().copied().max().unwrap_or(0);
    rows(tableau, row_count)
        .into_iter()
        .flat_map(|row| row.into_iter().rev())
        .collect()
}

fn p_descent_mask(poset: &Poset, word: &[usize]) -> usize {
    word.windows(2)
        .enumerate()
        .filter(|(_, pair)| poset.lt(pair[1], pair[0]))
        .fold(0, |mask, (index, _)| mask | (1 << index))
}

fn reverse_descent_positions(mask: usize, size: usize) -> usize {
    (0..size.saturating_sub(1))
        .filter(|&position| mask & (1 << position) != 0)
        .fold(0, |reversed, position| {
            reversed | (1 << (size - 2 - position))
        })
}

fn standard_tableau_descent_mask(lambda: &[usize], entries: &[usize]) -> usize {
    let mut row_of = vec![0; entries.len()];
    let mut offset = 0;
    for (row, &length) in lambda.iter().enumerate() {
        for &value in &entries[offset..offset + length] {
            row_of[value] = row;
        }
        offset += length;
    }
    (0..entries.len().saturating_sub(1))
        .filter(|&value| row_of[value + 1] > row_of[value])
        .fold(0, |mask, value| mask | (1 << value))
}

fn p_word_inversion(poset: &Poset, word: &[usize]) -> usize {
    (0..word.len())
        .flat_map(|left| (left + 1..word.len()).map(move |right| (left, right)))
        .filter(|&(left, right)| word[left] > word[right] && poset.edge(word[left], word[right]))
        .count()
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum KpColumnEventKind {
    Empty,
    Append,
    OrdinaryBump,
    LadderCopy,
    LadderMove,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct KpColumnEvent {
    first_scan_position: usize,
    last_scan_position: usize,
    kind: KpColumnEventKind,
    source: Vec<usize>,
    chain_before: Vec<usize>,
    chain_after: Vec<usize>,
    emitted: Vec<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct KpColumnStep {
    column: Vec<usize>,
    remainder: Vec<Option<usize>>,
    appended_scan_positions: Vec<usize>,
    events: Vec<KpColumnEvent>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct KpInsertion {
    /// Columns from left to right, each stored bottom-to-top.
    p_columns: Vec<Vec<usize>>,
    /// Recording columns in the same convention, with zero-based labels.
    q_columns: Vec<Vec<usize>>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct KpInsertionTrace {
    passes: Vec<KpColumnStep>,
    raw_p_columns: Vec<Vec<usize>>,
    repaired_rank_five_climber: bool,
}

fn kp_complement(poset: &Poset, value: usize) -> usize {
    poset.n() - 1 - value
}

fn kp_less(poset: &Poset, dual: bool, left: usize, right: usize) -> bool {
    if dual {
        poset.lt(kp_complement(poset, right), kp_complement(poset, left))
    } else {
        poset.lt(left, right)
    }
}

fn kp_is_ladder(poset: &Poset, dual: bool, values: &[usize]) -> bool {
    let mut sorted = values.to_vec();
    if dual {
        for value in &mut sorted {
            *value = kp_complement(poset, *value);
        }
    }
    sorted.sort_unstable();
    sorted.dedup();
    sorted.len() == values.len()
        && (0..sorted.len()).all(|left| {
            (left + 1..sorted.len())
                .all(|right| poset.lt(sorted[left], sorted[right]) == (right >= left + 2))
        })
}

fn kp_column_step_from(
    poset: &Poset,
    word: &[Option<usize>],
    chain: &[usize],
    drag_positions: &BTreeSet<usize>,
    dual: bool,
) -> KpColumnStep {
    let source: Vec<Option<usize>> = word.iter().rev().copied().collect();
    let mut remainder = vec![None; source.len()];
    let mut active: Vec<usize> = chain.iter().rev().copied().collect();
    let mut events = Vec::new();
    let mut offset = 0;

    while offset < source.len() {
        let first_scan_position = offset + 1;
        let chain_before = active.clone();
        let Some(entry) = source[offset] else {
            let emitted = if drag_positions.contains(&offset) && !active.is_empty() {
                remainder[offset] = Some(active.remove(0));
                remainder[offset].into_iter().collect()
            } else {
                Vec::new()
            };
            events.push(KpColumnEvent {
                first_scan_position,
                last_scan_position: first_scan_position,
                kind: KpColumnEventKind::Empty,
                source: Vec::new(),
                chain_before,
                chain_after: active.clone(),
                emitted,
            });
            offset += 1;
            continue;
        };

        let predecessor = active.iter().rposition(|&old| old < entry);
        if predecessor.is_none() || kp_less(poset, dual, active[predecessor.unwrap()], entry) {
            let replacement = predecessor.map_or(0, |index| index + 1);
            let kind = if replacement == active.len() {
                active.push(entry);
                KpColumnEventKind::Append
            } else {
                remainder[offset] = Some(active[replacement]);
                active[replacement] = entry;
                KpColumnEventKind::OrdinaryBump
            };
            events.push(KpColumnEvent {
                first_scan_position,
                last_scan_position: first_scan_position,
                kind,
                source: vec![entry],
                chain_before,
                chain_after: active.clone(),
                emitted: remainder[offset].into_iter().collect(),
            });
            offset += 1;
            continue;
        }

        let row = predecessor.expect("the ordinary case handles the bottom sentinel");
        let mut choices = Vec::new();
        for height in 0..active.len() - row {
            for width in 0..source.len() - offset {
                let Some(source_block) = source[offset..=offset + width]
                    .iter()
                    .copied()
                    .collect::<Option<Vec<_>>>()
                else {
                    continue;
                };
                if source_block.windows(2).any(|pair| pair[0] >= pair[1]) {
                    continue;
                }
                let mut ladder = active[row..=row + height].to_vec();
                ladder.extend(source_block);
                if kp_is_ladder(poset, dual, &ladder) {
                    choices.push((height, width));
                }
            }
        }
        let height = choices
            .iter()
            .map(|&(height, _)| height)
            .max()
            .expect("an incomparable pair is a two-element ladder");
        let width = choices
            .iter()
            .filter_map(|&(candidate_height, width)| (candidate_height == height).then_some(width))
            .max()
            .unwrap();
        let source_block: Vec<usize> = source[offset..=offset + width]
            .iter()
            .map(|value| value.expect("a selected source block has no empty positions"))
            .collect();

        let kind = if source_block[width] < active[row + height] {
            for (block_offset, &value) in source_block.iter().enumerate() {
                remainder[offset + block_offset] = Some(value);
            }
            KpColumnEventKind::LadderCopy
        } else {
            let old_active = active.clone();
            for index in row..=row + height {
                let first = source_block
                    .iter()
                    .position(|&value| value > old_active[index])
                    .expect("a ladder move has a first source cut");
                let last = if index == row + height {
                    width
                } else {
                    (0..width)
                        .rev()
                        .find(|&source_index| source_block[source_index] < old_active[index + 1])
                        .expect("a ladder move has a last source cut")
                };
                assert!(first <= last);
                let emitted = std::iter::once(old_active[index])
                    .chain(source_block[first..last].iter().copied());
                for (target, value) in (offset + first..=offset + last).zip(emitted) {
                    if let Some(old) = remainder[target] {
                        assert_eq!(old, value);
                    }
                    remainder[target] = Some(value);
                }
                active[index] = source_block[last];
            }
            KpColumnEventKind::LadderMove
        };
        events.push(KpColumnEvent {
            first_scan_position,
            last_scan_position: first_scan_position + width,
            kind,
            source: source_block,
            chain_before,
            chain_after: active.clone(),
            emitted: remainder[offset..=offset + width]
                .iter()
                .filter_map(|&value| value)
                .collect(),
        });
        offset += width + 1;
    }

    let appended_scan_positions = source
        .iter()
        .zip(&remainder)
        .enumerate()
        .filter_map(|(position, (old, new))| (old.is_some() && new.is_none()).then_some(position))
        .collect();
    active.reverse();
    remainder.reverse();
    KpColumnStep {
        column: active,
        remainder,
        appended_scan_positions,
        events,
    }
}

fn kp_column_step(poset: &Poset, word: &[Option<usize>]) -> KpColumnStep {
    kp_column_step_from(poset, word, &[], &BTreeSet::new(), false)
}

fn kp_reverse_complement(poset: &Poset, values: &[Option<usize>]) -> Vec<Option<usize>> {
    values
        .iter()
        .rev()
        .map(|value| value.map(|value| kp_complement(poset, value)))
        .collect()
}

fn kp_reverse_complement_column(poset: &Poset, values: &[usize]) -> Vec<usize> {
    values
        .iter()
        .rev()
        .map(|&value| kp_complement(poset, value))
        .collect()
}

fn kp_rank_five_repair(poset: &Poset, insertion: &mut KpInsertion) -> bool {
    if poset.code() != [2, 4, 4, 5, 5] || insertion.p_columns != [vec![4, 2], vec![3, 0], vec![1]] {
        return false;
    }
    let first_q = [vec![2, 0], vec![3, 1], vec![4]];
    let second_q = [vec![1, 0], vec![3, 2], vec![4]];
    if insertion.q_columns != first_q && insertion.q_columns != second_q {
        return false;
    }
    insertion.p_columns = vec![vec![4, 1], vec![3, 0], vec![2]];
    true
}

fn kp_rank_five_unrepair(poset: &Poset, insertion: &mut KpInsertion) -> bool {
    if poset.code() != [2, 4, 4, 5, 5] || insertion.p_columns != [vec![4, 1], vec![3, 0], vec![2]] {
        return false;
    }
    let first_q = [vec![2, 0], vec![3, 1], vec![4]];
    let second_q = [vec![1, 0], vec![3, 2], vec![4]];
    if insertion.q_columns != first_q && insertion.q_columns != second_q {
        return false;
    }
    insertion.p_columns = vec![vec![4, 2], vec![3, 0], vec![1]];
    true
}

fn kp_insert(
    poset: &Poset,
    word: &[usize],
    repair_rank_five: bool,
) -> (KpInsertion, KpInsertionTrace) {
    assert_eq!(word.len(), poset.n());
    assert_eq!(
        word.iter().copied().collect::<BTreeSet<_>>().len(),
        word.len()
    );
    let mut remainder: Vec<Option<usize>> = word.iter().copied().map(Some).collect();
    let mut p_columns = Vec::new();
    let mut q_columns = Vec::new();
    let mut passes = Vec::new();
    while remainder.iter().any(Option::is_some) {
        let step = kp_column_step(poset, &remainder);
        let mut recording = step.appended_scan_positions.clone();
        recording.reverse();
        assert_eq!(step.column.len(), recording.len());
        p_columns.push(step.column.clone());
        q_columns.push(recording);
        remainder = step.remainder.clone();
        passes.push(step);
    }
    let raw_p_columns = p_columns.clone();
    let mut insertion = KpInsertion {
        p_columns,
        q_columns,
    };
    let repaired_rank_five_climber = repair_rank_five && kp_rank_five_repair(poset, &mut insertion);
    (
        insertion,
        KpInsertionTrace {
            passes,
            raw_p_columns,
            repaired_rank_five_climber,
        },
    )
}

fn kp_inverse_checked(
    poset: &Poset,
    insertion: &KpInsertion,
    unrepair_rank_five: bool,
) -> Option<Vec<usize>> {
    if insertion.p_columns.len() != insertion.q_columns.len() {
        return None;
    }
    let mut raw = insertion.clone();
    if unrepair_rank_five {
        kp_rank_five_unrepair(poset, &mut raw);
    }
    let mut remainder = vec![None; poset.n()];
    for (column, recording) in raw.p_columns.iter().zip(&raw.q_columns).rev() {
        let drags: BTreeSet<usize> = recording
            .iter()
            .map(|&scan_position| poset.n() - 1 - scan_position)
            .collect();
        let hatted_remainder = kp_reverse_complement(poset, &remainder);
        let hatted_column = kp_reverse_complement_column(poset, column);
        let step = kp_column_step_from(poset, &hatted_remainder, &hatted_column, &drags, true);
        if !step.column.is_empty() {
            return None;
        }
        remainder = kp_reverse_complement(poset, &step.remainder);
    }
    remainder.into_iter().collect()
}

fn kp_inverse(poset: &Poset, insertion: &KpInsertion, unrepair_rank_five: bool) -> Vec<usize> {
    kp_inverse_checked(poset, insertion, unrepair_rank_five)
        .expect("a complete KP inverse must have no residual column or empty slots")
}

fn kp_columns_to_rows(columns: &[Vec<usize>]) -> Vec<Vec<usize>> {
    if columns.is_empty() {
        return Vec::new();
    }
    assert!(columns
        .windows(2)
        .all(|pair| pair[0].len() >= pair[1].len()));
    let mut rows = Vec::new();
    for row in 0..columns[0].len() {
        rows.push(
            columns
                .iter()
                .filter(|column| row < column.len())
                .map(|column| column[column.len() - 1 - row])
                .collect(),
        );
    }
    rows
}

fn kp_has_partition_shape(columns: &[Vec<usize>]) -> bool {
    columns
        .windows(2)
        .all(|pair| pair[0].len() >= pair[1].len())
}

fn kp_rows_to_columns(rows: &[Vec<usize>]) -> Vec<Vec<usize>> {
    if rows.is_empty() {
        return Vec::new();
    }
    assert!(rows.windows(2).all(|pair| pair[0].len() >= pair[1].len()));
    (0..rows[0].len())
        .map(|col| {
            rows.iter()
                .filter_map(|row| row.get(col).copied())
                .rev()
                .collect()
        })
        .collect()
}

fn kp_tableau_key(insertion: &KpInsertion) -> (Vec<usize>, Vec<usize>, Vec<usize>) {
    let p_rows = kp_columns_to_rows(&insertion.p_columns);
    let q_rows = kp_columns_to_rows(&insertion.q_columns);
    let lambda = p_rows.iter().map(Vec::len).collect::<Vec<_>>();
    assert_eq!(lambda, q_rows.iter().map(Vec::len).collect::<Vec<_>>());
    (
        lambda,
        p_rows.into_iter().flatten().collect(),
        q_rows.into_iter().flatten().collect(),
    )
}

fn kp_is_p_tableau(poset: &Poset, columns: &[Vec<usize>]) -> bool {
    if !kp_has_partition_shape(columns) {
        return false;
    }
    let rows = kp_columns_to_rows(columns);
    rows.iter()
        .all(|row| row.windows(2).all(|pair| !poset.lt(pair[1], pair[0])))
        && rows.windows(2).all(|pair| {
            pair[1]
                .iter()
                .zip(&pair[0])
                .all(|(&lower, &upper)| poset.lt(upper, lower))
        })
}

fn kp_is_standard_tableau(columns: &[Vec<usize>]) -> bool {
    if !kp_has_partition_shape(columns) {
        return false;
    }
    let rows = kp_columns_to_rows(columns);
    rows.iter()
        .all(|row| row.windows(2).all(|pair| pair[0] < pair[1]))
        && rows.windows(2).all(|pair| {
            pair[1]
                .iter()
                .zip(&pair[0])
                .all(|(&lower, &upper)| upper < lower)
        })
}

fn kp_recording_descent_mask(columns: &[Vec<usize>]) -> usize {
    let size: usize = columns.iter().map(Vec::len).sum();
    let mut row_of = vec![usize::MAX; size];
    for column in columns {
        for (bottom_offset, &value) in column.iter().enumerate() {
            assert!(value < size);
            assert_eq!(row_of[value], usize::MAX);
            row_of[value] = column.len() - 1 - bottom_offset;
        }
    }
    assert!(row_of.iter().all(|&row| row != usize::MAX));
    (0..size.saturating_sub(1))
        .filter(|&value| row_of[value + 1] > row_of[value])
        .fold(0, |mask, value| mask | (1 << value))
}

fn kp_expected_targets(poset: &Poset) -> BTreeSet<(Vec<usize>, Vec<usize>, Vec<usize>)> {
    let n = poset.n();
    let mut targets = BTreeSet::new();
    for lambda in partitions(n) {
        let conjugate = conjugate_partition(&lambda);
        let p_entries: Vec<Vec<usize>> = p_tableaux(poset, &conjugate)
            .into_iter()
            .map(|tableau| {
                let conjugate_entries: Vec<usize> = rows(&tableau, conjugate.len())
                    .into_iter()
                    .flatten()
                    .collect();
                let (actual_shape, entries) = transpose_tableau(&conjugate, &conjugate_entries);
                assert_eq!(actual_shape, lambda);
                entries
            })
            .collect();
        let standard = ssyts(&lambda, &vec![1; n]);
        for p in &p_entries {
            let p_columns = kp_rows_to_columns(&entries_to_rows(&lambda, p, false));
            assert!(kp_is_p_tableau(poset, &p_columns));
            for q in &standard {
                assert!(targets.insert((lambda.clone(), p.clone(), q.clone())));
            }
        }
    }
    targets
}

fn kp_trace_checksum(trace: &KpInsertionTrace) -> usize {
    let mut checksum = usize::from(trace.repaired_rank_five_climber);
    for pass in &trace.passes {
        checksum = checksum
            .wrapping_mul(131)
            .wrapping_add(pass.appended_scan_positions.len())
            .wrapping_add(pass.column.len())
            .wrapping_add(
                pass.remainder
                    .iter()
                    .filter(|entry| entry.is_some())
                    .count(),
            );
        for event in &pass.events {
            checksum = checksum
                .wrapping_mul(131)
                .wrapping_add(event.first_scan_position)
                .wrapping_add(event.last_scan_position)
                .wrapping_add(event.kind as usize)
                .wrapping_add(event.source.iter().sum::<usize>())
                .wrapping_add(event.chain_before.iter().sum::<usize>())
                .wrapping_add(event.chain_after.iter().sum::<usize>())
                .wrapping_add(event.emitted.iter().sum::<usize>());
        }
    }
    checksum
}

#[derive(Clone, Debug)]
struct KpDefectWitness {
    code: Vec<usize>,
    word: Vec<usize>,
    insertion: KpInsertion,
}

#[derive(Default)]
struct KpCensus {
    posets: usize,
    ineligible_posets: usize,
    defective_posets: usize,
    words: usize,
    raw_invalid_p: usize,
    raw_invalid_q: usize,
    repaired_words: usize,
    corrected_invalid_p: usize,
    corrected_collisions: usize,
    corrected_missing_targets: usize,
    trace_checksum: usize,
    first_defect: Option<KpDefectWitness>,
}

#[derive(Default)]
struct KpRawCensus {
    posets: usize,
    ineligible_posets: usize,
    defective_posets: usize,
    words: usize,
    invalid_p: usize,
    invalid_q: usize,
    nonpartition_p: usize,
    nonpartition_q: usize,
    collisions: usize,
    shape_compositions: BTreeMap<Vec<usize>, usize>,
    first_defect: Option<KpDefectWitness>,
}

type KpTableauKey = (Vec<usize>, Vec<usize>, Vec<usize>);
type KpFiber = (usize, usize);
type KpInvalidFiber = BTreeMap<KpFiber, Vec<(Vec<usize>, KpInsertion)>>;
type KpRecording = Vec<Vec<usize>>;
type KpRecordingHeight = (KpRecording, usize);
type KpInvalidByRecording = BTreeMap<KpRecordingHeight, Vec<(Vec<usize>, KpInsertion)>>;
type KpSource = (Vec<usize>, KpInsertion);
type KpMatchedPair = (KpSource, KpInsertion);

struct KpMinimumMovementMatching {
    pairs: Vec<KpMatchedPair>,
    residual_sources: Vec<KpSource>,
    residual_targets: Vec<KpInsertion>,
    total_optimum_count: usize,
    profile_optimum_count: usize,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct KpCellAction {
    source_column_shape: Vec<usize>,
    target_column_shape: Vec<usize>,
    moves: Vec<((usize, usize), (usize, usize))>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct KpPairAction {
    p: KpCellAction,
    q: KpCellAction,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct KpLocalSignature {
    column_shape: Vec<usize>,
    window_occupancy: Vec<(usize, usize)>,
    comparison_code: u128,
    recording_descent_mask: usize,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct KpStructuralSignature {
    column_shape: Vec<usize>,
    p_relations: Vec<u8>,
    natural_relations: Option<Vec<bool>>,
    recording: Option<KpRecording>,
    recording_descent_mask: usize,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct KpBoundarySignature {
    column_shape: Vec<usize>,
    boundary: (usize, usize, usize),
    window_occupancy: Vec<(usize, usize)>,
    comparison_code: u128,
    recording_columns: Vec<Vec<usize>>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct KpLocalPKnuthCertificate {
    margin: usize,
    first: usize,
    last: usize,
    distance: usize,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct KpTargetSignature {
    column_shape: Vec<usize>,
    window_occupancy: Vec<(usize, usize)>,
    comparison_code: u128,
    recording: KpRecording,
}

struct KpCorrectionCatalog {
    forward: BTreeMap<Vec<usize>, KpInsertion>,
    reverse: BTreeMap<KpInsertion, Vec<usize>>,
    defects: Vec<(Vec<usize>, KpInsertion, KpInsertion)>,
    max_defect_fiber: usize,
    ambiguous_defect_fibers: usize,
    first_ambiguous_fiber: Option<KpAmbiguousFiber>,
    max_residual_fiber: usize,
    ambiguous_residual_fibers: usize,
    first_ambiguous_residual: Option<KpAmbiguousFiber>,
    max_exact_q_group: usize,
    ambiguous_exact_q_groups: usize,
    first_ambiguous_exact_q: Option<KpAmbiguousFiber>,
    minimum_movement_groups: usize,
    ambiguous_minimum_movement_groups: usize,
    max_minimum_movement_optima: usize,
    first_ambiguous_minimum_movement: Option<KpAmbiguousFiber>,
    ambiguous_movement_profile_groups: usize,
    max_movement_profile_optima: usize,
    first_ambiguous_movement_profile: Option<KpAmbiguousFiber>,
    max_exact_height_group: usize,
    ambiguous_exact_height_groups: usize,
    ambiguous_height_movement_groups: usize,
    ambiguous_height_profile_groups: usize,
    max_height_profile_optima: usize,
    first_ambiguous_height_profile: Option<KpAmbiguousFiber>,
}

#[derive(Clone, Debug)]
struct KpAmbiguousFiber {
    recording_descent_mask: usize,
    sources: Vec<(Vec<usize>, KpInsertion)>,
    targets: Vec<KpInsertion>,
}

fn kp_insertion_from_key(key: &KpTableauKey) -> KpInsertion {
    let (lambda, p, q) = key;
    KpInsertion {
        p_columns: kp_rows_to_columns(&entries_to_rows(lambda, p, false)),
        q_columns: kp_rows_to_columns(&entries_to_rows(lambda, q, false)),
    }
}

fn kp_insertion_reading_word(insertion: &KpInsertion) -> Vec<usize> {
    insertion.p_columns.iter().flatten().copied().collect()
}

fn kp_column_cell_action(source: &[Vec<usize>], target: &[Vec<usize>]) -> KpCellAction {
    fn coordinates(columns: &[Vec<usize>]) -> BTreeMap<usize, (usize, usize)> {
        let mut coordinates = BTreeMap::new();
        for (col, column) in columns.iter().enumerate() {
            for (bottom_offset, &value) in column.iter().enumerate() {
                let row = column.len() - 1 - bottom_offset;
                assert!(coordinates.insert(value, (row, col)).is_none());
            }
        }
        coordinates
    }
    let source_coordinates = coordinates(source);
    let target_coordinates = coordinates(target);
    let mut moves: Vec<_> = source_coordinates
        .iter()
        .filter_map(|(&value, &from)| {
            let to = target_coordinates[&value];
            (from != to).then_some((from, to))
        })
        .collect();
    moves.sort();
    KpCellAction {
        source_column_shape: source.iter().map(Vec::len).collect(),
        target_column_shape: target.iter().map(Vec::len).collect(),
        moves,
    }
}

fn kp_cell_action(source: &KpInsertion, target: &KpInsertion) -> KpCellAction {
    kp_column_cell_action(&source.p_columns, &target.p_columns)
}

fn kp_pair_action(source: &KpInsertion, target: &KpInsertion) -> KpPairAction {
    KpPairAction {
        p: kp_column_cell_action(&source.p_columns, &target.p_columns),
        q: kp_column_cell_action(&source.q_columns, &target.q_columns),
    }
}

fn kp_cell_action_cost(action: &KpCellAction) -> (usize, usize) {
    let distance = action
        .moves
        .iter()
        .map(|&(from, to)| from.0.abs_diff(to.0) + from.1.abs_diff(to.1))
        .sum();
    (action.moves.len(), distance)
}

fn kp_pair_action_cost(source: &KpInsertion, target: &KpInsertion) -> [usize; 4] {
    let action = kp_pair_action(source, target);
    let (p_moves, p_distance) = kp_cell_action_cost(&action.p);
    let (q_moves, q_distance) = kp_cell_action_cost(&action.q);
    [
        p_moves + q_moves,
        p_distance + q_distance,
        q_moves,
        q_distance,
    ]
}

fn kp_minimum_movement_matching(
    sources: &[KpSource],
    targets: &[KpInsertion],
) -> KpMinimumMovementMatching {
    assert!(!sources.is_empty() && !targets.is_empty());
    let mut assignments = BTreeSet::new();
    if sources.len() <= targets.len() {
        for permutation in permutations(targets.len()) {
            assignments.insert(
                permutation[..sources.len()]
                    .iter()
                    .copied()
                    .map(Some)
                    .collect::<Vec<_>>(),
            );
        }
    } else {
        for permutation in permutations(sources.len()) {
            let mut assignment = vec![None; sources.len()];
            for (target_index, &source_index) in permutation[..targets.len()].iter().enumerate() {
                assignment[source_index] = Some(target_index);
            }
            assignments.insert(assignment);
        }
    }
    let mut candidates = Vec::new();
    for assignment in assignments {
        let mut total = [0; 4];
        let mut profile = Vec::new();
        for (source, target_index) in sources.iter().zip(&assignment) {
            if let Some(target_index) = target_index {
                let cost = kp_pair_action_cost(&source.1, &targets[*target_index]);
                for (entry, value) in total.iter_mut().zip(cost) {
                    *entry += value;
                }
                profile.push(cost);
            }
        }
        profile.sort_by(|left, right| right.cmp(left));
        candidates.push((total, profile, assignment));
    }
    candidates.sort();
    let (best_total, best_profile, best_assignment) = &candidates[0];
    let total_optimum_count = candidates
        .iter()
        .take_while(|(total, _, _)| total == best_total)
        .count();
    let profile_optimum_count = candidates
        .iter()
        .take_while(|(total, profile, _)| total == best_total && profile == best_profile)
        .count();
    let mut used_targets = vec![false; targets.len()];
    let mut pairs = Vec::new();
    let mut residual_sources = Vec::new();
    for (source, target_index) in sources.iter().cloned().zip(best_assignment) {
        if let Some(target_index) = target_index {
            used_targets[*target_index] = true;
            pairs.push((source, targets[*target_index].clone()));
        } else {
            residual_sources.push(source);
        }
    }
    let residual_targets = targets
        .iter()
        .cloned()
        .zip(used_targets)
        .filter_map(|(target, used)| (!used).then_some(target))
        .collect();
    KpMinimumMovementMatching {
        pairs,
        residual_sources,
        residual_targets,
        total_optimum_count,
        profile_optimum_count,
    }
}

fn kp_minimum_movement_edge_matching(
    sources: &[KpSource],
    targets: &[KpInsertion],
    edges: &BTreeMap<Vec<usize>, BTreeSet<KpInsertion>>,
) -> KpMinimumMovementMatching {
    fn assignments(
        source_index: usize,
        sources: &[KpSource],
        targets: &[KpInsertion],
        edges: &BTreeMap<Vec<usize>, BTreeSet<KpInsertion>>,
        used_targets: &mut BTreeSet<usize>,
        current: &mut Vec<Option<usize>>,
        result: &mut Vec<Vec<Option<usize>>>,
    ) {
        if source_index == sources.len() {
            result.push(current.clone());
            return;
        }
        current.push(None);
        assignments(
            source_index + 1,
            sources,
            targets,
            edges,
            used_targets,
            current,
            result,
        );
        current.pop();
        for (target_index, target) in targets.iter().enumerate() {
            if used_targets.contains(&target_index)
                || !edges
                    .get(&sources[source_index].0)
                    .is_some_and(|neighbors| neighbors.contains(target))
            {
                continue;
            }
            used_targets.insert(target_index);
            current.push(Some(target_index));
            assignments(
                source_index + 1,
                sources,
                targets,
                edges,
                used_targets,
                current,
                result,
            );
            current.pop();
            used_targets.remove(&target_index);
        }
    }

    assert!(!sources.is_empty() && !targets.is_empty());
    let mut all_assignments = Vec::new();
    assignments(
        0,
        sources,
        targets,
        edges,
        &mut BTreeSet::new(),
        &mut Vec::new(),
        &mut all_assignments,
    );
    let mut candidates = Vec::new();
    for assignment in all_assignments {
        let mut total = [0; 4];
        let mut profile = Vec::new();
        for (source, target_index) in sources.iter().zip(&assignment) {
            if let Some(target_index) = target_index {
                let cost = kp_pair_action_cost(&source.1, &targets[*target_index]);
                for (entry, value) in total.iter_mut().zip(cost) {
                    *entry += value;
                }
                profile.push(cost);
            }
        }
        profile.sort_by(|left, right| right.cmp(left));
        let unmatched = assignment.iter().filter(|target| target.is_none()).count();
        candidates.push((unmatched, total, profile, assignment));
    }
    candidates.sort();
    let (best_unmatched, best_total, best_profile, best_assignment) = &candidates[0];
    let total_optimum_count = candidates
        .iter()
        .take_while(|(unmatched, total, _, _)| unmatched == best_unmatched && total == best_total)
        .count();
    let profile_optimum_count = candidates
        .iter()
        .take_while(|(unmatched, total, profile, _)| {
            unmatched == best_unmatched && total == best_total && profile == best_profile
        })
        .count();
    let mut used_targets = vec![false; targets.len()];
    let mut pairs = Vec::new();
    let mut residual_sources = Vec::new();
    for (source, target_index) in sources.iter().cloned().zip(best_assignment) {
        if let Some(target_index) = target_index {
            used_targets[*target_index] = true;
            pairs.push((source, targets[*target_index].clone()));
        } else {
            residual_sources.push(source);
        }
    }
    let residual_targets = targets
        .iter()
        .cloned()
        .zip(used_targets)
        .filter_map(|(target, used)| (!used).then_some(target))
        .collect();
    KpMinimumMovementMatching {
        pairs,
        residual_sources,
        residual_targets,
        total_optimum_count,
        profile_optimum_count,
    }
}

fn kp_apply_cell_action(columns: &[Vec<usize>], action: &KpCellAction) -> Vec<Vec<usize>> {
    assert_eq!(
        columns.iter().map(Vec::len).collect::<Vec<_>>(),
        action.source_column_shape
    );
    let mut target_columns: Vec<Vec<Option<usize>>> = action
        .target_column_shape
        .iter()
        .map(|&height| vec![None; height])
        .collect();
    for (col, column) in columns.iter().enumerate() {
        for (bottom_offset, &value) in column.iter().enumerate() {
            let row = column.len() - 1 - bottom_offset;
            let destination = action
                .moves
                .iter()
                .find_map(|&(from, to)| (from == (row, col)).then_some(to))
                .unwrap_or((row, col));
            let target_height = action.target_column_shape[destination.1];
            assert!(destination.0 < target_height);
            let slot = &mut target_columns[destination.1][target_height - 1 - destination.0];
            assert!(slot.replace(value).is_none());
        }
    }
    target_columns
        .into_iter()
        .map(|column| {
            column
                .into_iter()
                .map(|entry| entry.expect("a cell action fills its target shape"))
                .collect()
        })
        .collect()
}

fn kp_apply_pair_action(insertion: &KpInsertion, action: &KpPairAction) -> KpInsertion {
    KpInsertion {
        p_columns: kp_apply_cell_action(&insertion.p_columns, &action.p),
        q_columns: kp_apply_cell_action(&insertion.q_columns, &action.q),
    }
}

fn kp_reverse_cell_action(action: &KpCellAction) -> KpCellAction {
    let mut moves: Vec<_> = action.moves.iter().map(|&(from, to)| (to, from)).collect();
    moves.sort();
    KpCellAction {
        source_column_shape: action.target_column_shape.clone(),
        target_column_shape: action.source_column_shape.clone(),
        moves,
    }
}

fn kp_reverse_pair_action(action: &KpPairAction) -> KpPairAction {
    KpPairAction {
        p: kp_reverse_cell_action(&action.p),
        q: kp_reverse_cell_action(&action.q),
    }
}

fn kp_local_signature(poset: &Poset, insertion: &KpInsertion) -> KpLocalSignature {
    let mut window = Vec::new();
    let mut occupancy = Vec::new();
    for (col, column) in insertion.p_columns.iter().enumerate().take(4) {
        for row in 0..column.len().min(2) {
            let entry = column[column.len() - 1 - row];
            occupancy.push((row, col));
            window.push(entry);
        }
    }
    let mut comparison_code = 0u128;
    let mut place = 1u128;
    for left in 0..window.len() {
        for right in left + 1..window.len() {
            let relation = if poset.lt(window[left], window[right]) {
                1
            } else if poset.lt(window[right], window[left]) {
                2
            } else {
                0
            };
            comparison_code += place * relation;
            place *= 3;
        }
    }
    KpLocalSignature {
        column_shape: insertion.p_columns.iter().map(Vec::len).collect(),
        window_occupancy: occupancy,
        comparison_code,
        recording_descent_mask: kp_recording_descent_mask(&insertion.q_columns),
    }
}

fn kp_structural_signature(
    poset: &Poset,
    insertion: &KpInsertion,
    include_natural_relations: bool,
    include_recording: bool,
) -> KpStructuralSignature {
    let entries: Vec<usize> = insertion.p_columns.iter().flatten().copied().collect();
    let mut p_relations = Vec::new();
    let mut natural_relations = include_natural_relations.then(Vec::new);
    for left in 0..entries.len() {
        for right in left + 1..entries.len() {
            p_relations.push(if poset.lt(entries[left], entries[right]) {
                1
            } else if poset.lt(entries[right], entries[left]) {
                2
            } else {
                0
            });
            if let Some(relations) = &mut natural_relations {
                relations.push(entries[left] < entries[right]);
            }
        }
    }
    KpStructuralSignature {
        column_shape: insertion.p_columns.iter().map(Vec::len).collect(),
        p_relations,
        natural_relations,
        recording: include_recording.then(|| insertion.q_columns.clone()),
        recording_descent_mask: kp_recording_descent_mask(&insertion.q_columns),
    }
}

fn kp_first_invalid_boundary(
    poset: &Poset,
    columns: &[Vec<usize>],
) -> Option<(usize, usize, usize)> {
    let mut violations = Vec::new();
    for boundary in 0..columns.len().saturating_sub(1) {
        if columns[boundary].len() < columns[boundary + 1].len() {
            violations.push((boundary, columns[boundary].len(), 0));
        }
        let common_height = columns[boundary].len().min(columns[boundary + 1].len());
        for row in 0..common_height {
            let left = columns[boundary][columns[boundary].len() - 1 - row];
            let right = columns[boundary + 1][columns[boundary + 1].len() - 1 - row];
            if poset.lt(right, left) {
                violations.push((boundary, row, 1));
            }
        }
    }
    violations.into_iter().min()
}

fn kp_boundary_signature_checked(
    poset: &Poset,
    insertion: &KpInsertion,
) -> Option<KpBoundarySignature> {
    let boundary = kp_first_invalid_boundary(poset, &insertion.p_columns)?;
    let mut window = Vec::new();
    let mut occupancy = Vec::new();
    let first_col = boundary.0.saturating_sub(1);
    let last_col = (boundary.0 + 4).min(insertion.p_columns.len() - 1);
    let first_row = boundary.1.saturating_sub(1);
    let last_row = boundary.1 + 1;
    for col in first_col..=last_col {
        let column = &insertion.p_columns[col];
        for row in first_row..=last_row.min(column.len().saturating_sub(1)) {
            occupancy.push((row, col));
            window.push(column[column.len() - 1 - row]);
        }
    }
    let mut comparison_code = 0u128;
    let mut place = 1u128;
    for left in 0..window.len() {
        for right in left + 1..window.len() {
            let relation = if poset.lt(window[left], window[right]) {
                1
            } else if poset.lt(window[right], window[left]) {
                2
            } else {
                0
            };
            comparison_code += place * relation;
            place *= 3;
        }
    }
    Some(KpBoundarySignature {
        column_shape: insertion.p_columns.iter().map(Vec::len).collect(),
        boundary,
        window_occupancy: occupancy,
        comparison_code,
        recording_columns: insertion.q_columns[boundary.0..=boundary.0 + 1].to_vec(),
    })
}

fn kp_boundary_signature(poset: &Poset, insertion: &KpInsertion) -> KpBoundarySignature {
    kp_boundary_signature_checked(poset, insertion)
        .expect("a bad KP output has a shape or row violation")
}

fn kp_shape_boundary_repair(poset: &Poset, insertion: &KpInsertion) -> Option<KpInsertion> {
    let (boundary, row, kind) = kp_first_invalid_boundary(poset, &insertion.p_columns)?;
    if kind != 0
        || row != 2
        || boundary + 3 >= insertion.p_columns.len()
        || insertion.p_columns[boundary].len() != 2
        || insertion.p_columns[boundary + 1].len() != 3
        || insertion.p_columns[boundary + 2].len() != 1
        || insertion.p_columns[boundary + 3].len() != 1
    {
        return None;
    }
    let tall = &insertion.p_columns[boundary + 1];
    let (c, b, a) = (tall[0], tall[1], tall[2]);
    let d = insertion.p_columns[boundary + 2][0];
    let e = insertion.p_columns[boundary + 3][0];
    let mut repaired = insertion.clone();
    repaired.p_columns[boundary + 1] = vec![c, e];
    repaired.p_columns[boundary + 2] = vec![d, a];
    repaired.p_columns[boundary + 3] = vec![b];
    let recording_entry = repaired.q_columns[boundary + 1].remove(0);
    repaired.q_columns[boundary + 2].insert(0, recording_entry);
    Some(repaired)
}

fn kp_recording_shape_repair_candidates(insertion: &KpInsertion) -> Vec<KpRecording> {
    let shape: Vec<_> = insertion.q_columns.iter().map(Vec::len).collect();
    let mut candidates = Vec::new();
    match shape.as_slice() {
        [2, 2, 1, 1, 1] => {
            let mut direct = insertion.q_columns[..4].to_vec();
            direct[2].insert(0, insertion.q_columns[4][0]);
            candidates.push(direct);

            let mut shifted = insertion.q_columns[..4].to_vec();
            let shifted_entry = shifted[3][0];
            shifted[2].insert(0, shifted_entry);
            shifted[3][0] = insertion.q_columns[4][0];
            candidates.push(shifted);
        }
        [2, 3, 1, 1] => {
            let mut right = insertion.q_columns.clone();
            let entry = right[1].remove(0);
            right[2].insert(0, entry);
            candidates.push(right);

            let mut left = insertion.q_columns.clone();
            let entry = left[1].remove(0);
            left[0].insert(0, entry);
            candidates.push(left);
        }
        [3, 2, 1, 1] => {
            let mut left = insertion.q_columns[..3].to_vec();
            left[2].insert(0, insertion.q_columns[3][0]);
            candidates.push(left);
        }
        _ => {}
    }
    let descent_mask = kp_recording_descent_mask(&insertion.q_columns);
    candidates.retain(|candidate| {
        kp_is_standard_tableau(candidate) && kp_recording_descent_mask(candidate) == descent_mask
    });
    candidates.sort();
    candidates.dedup();
    candidates
}

fn kp_boundary_transposition_repairs(poset: &Poset, insertion: &KpInsertion) -> Vec<KpInsertion> {
    let Some((boundary, row, kind)) = kp_first_invalid_boundary(poset, &insertion.p_columns) else {
        return Vec::new();
    };
    if kind != 1 {
        return Vec::new();
    }
    let mut candidates = Vec::new();
    for (column_delta, row_delta) in [(2, 0), (3, 0), (4, 0), (2, -1), (2, 1)] {
        let target_col = boundary + column_delta;
        let Some(target_row) = row.checked_add_signed(row_delta) else {
            continue;
        };
        if target_col >= insertion.p_columns.len()
            || target_row >= insertion.p_columns[target_col].len()
        {
            continue;
        }
        let mut candidate = insertion.clone();
        let left_index = candidate.p_columns[boundary].len() - 1 - row;
        let target_index = candidate.p_columns[target_col].len() - 1 - target_row;
        let left = candidate.p_columns[boundary][left_index];
        let right = candidate.p_columns[target_col][target_index];
        candidate.p_columns[boundary][left_index] = right;
        candidate.p_columns[target_col][target_index] = left;
        if !kp_is_p_tableau(poset, &candidate.p_columns)
            || !kp_is_standard_tableau(&candidate.q_columns)
        {
            continue;
        }
        if kp_inverse_checked(poset, &candidate, false)
            .is_some_and(|word| kp_insert(poset, &word, false).0 == candidate)
        {
            continue;
        }
        if !kp_margin_one_p_knuth_reachable(poset, insertion, &candidate) {
            continue;
        }
        candidates.push((column_delta + row.abs_diff(target_row), candidate));
    }
    candidates.sort();
    let Some(minimum) = candidates.first().map(|candidate| candidate.0) else {
        return Vec::new();
    };
    candidates
        .into_iter()
        .take_while(|candidate| candidate.0 == minimum)
        .map(|candidate| candidate.1)
        .collect()
}

fn kp_margin_one_p_knuth_reachable(
    poset: &Poset,
    source: &KpInsertion,
    target: &KpInsertion,
) -> bool {
    kp_local_p_knuth_certificate(poset, source, target, 1).is_some()
}

fn kp_local_p_knuth_certificate(
    poset: &Poset,
    source: &KpInsertion,
    target: &KpInsertion,
    max_margin: usize,
) -> Option<KpLocalPKnuthCertificate> {
    let source_word = kp_insertion_reading_word(source);
    let target_word = kp_insertion_reading_word(target);
    if source_word.len() != target_word.len() || source_word.is_empty() {
        return None;
    }
    let changed: Vec<usize> = source_word
        .iter()
        .zip(&target_word)
        .enumerate()
        .filter_map(|(index, (left, right))| (left != right).then_some(index))
        .collect();
    if changed.is_empty() {
        return None;
    }
    for margin in 0..=max_margin {
        let first = changed[0].saturating_sub(margin);
        let last = (changed[changed.len() - 1] + margin).min(source_word.len() - 1);
        let source_interval = source_word[first..=last].to_vec();
        let target_interval = target_word[first..=last].to_vec();
        let mut distances = BTreeMap::from([(source_interval.clone(), 0)]);
        let mut queue = VecDeque::from([source_interval]);
        while let Some(word) = queue.pop_front() {
            let distance = distances[&word];
            if word == target_interval {
                return Some(KpLocalPKnuthCertificate {
                    margin,
                    first,
                    last,
                    distance,
                });
            }
            for neighbor in p_knuth_neighbors(poset, &word) {
                if !distances.contains_key(&neighbor) {
                    distances.insert(neighbor.clone(), distance + 1);
                    queue.push_back(neighbor);
                }
            }
        }
    }
    None
}

fn kp_asymmetric_p_knuth_certificate(
    poset: &Poset,
    source: &KpInsertion,
    target: &KpInsertion,
    before: usize,
    after: usize,
) -> Option<KpLocalPKnuthCertificate> {
    let source_word = kp_insertion_reading_word(source);
    let target_word = kp_insertion_reading_word(target);
    if source_word.len() != target_word.len() || source_word.is_empty() {
        return None;
    }
    let changed: Vec<usize> = source_word
        .iter()
        .zip(&target_word)
        .enumerate()
        .filter_map(|(index, (left, right))| (left != right).then_some(index))
        .collect();
    if changed.is_empty() {
        return None;
    }
    let first = changed[0].saturating_sub(before);
    let last = (changed[changed.len() - 1] + after).min(source_word.len() - 1);
    let source_interval = source_word[first..=last].to_vec();
    let target_interval = target_word[first..=last].to_vec();
    let mut distances = BTreeMap::from([(source_interval.clone(), 0)]);
    let mut queue = VecDeque::from([source_interval]);
    while let Some(word) = queue.pop_front() {
        let distance = distances[&word];
        if word == target_interval {
            return Some(KpLocalPKnuthCertificate {
                margin: before.max(after),
                first,
                last,
                distance,
            });
        }
        for neighbor in p_knuth_neighbors(poset, &word) {
            if !distances.contains_key(&neighbor) {
                distances.insert(neighbor.clone(), distance + 1);
                queue.push_back(neighbor);
            }
        }
    }
    None
}

type KpCandidateEdges = BTreeMap<Vec<usize>, BTreeSet<KpInsertion>>;

struct KpUniformGraphCatalog {
    pairs: Vec<KpMatchedPair>,
    source_count: usize,
    edge_count: usize,
    target_count: usize,
    valid_p_bad_q_count: usize,
    wrong_raw_descent_count: usize,
    stage_pair_counts: [usize; 3],
    stage_component_counts: [usize; 3],
    total_cost_ties: usize,
    profile_ties: usize,
    max_source_component: usize,
    max_target_component: usize,
    unmatched_sources: Vec<KpSource>,
    unmatched_targets: Vec<KpInsertion>,
}

fn kp_cell_entries(columns: &[Vec<usize>]) -> BTreeMap<(usize, usize), usize> {
    let mut entries = BTreeMap::new();
    for (col, column) in columns.iter().enumerate() {
        for (bottom_offset, &value) in column.iter().enumerate() {
            let row = column.len() - 1 - bottom_offset;
            assert!(entries.insert((row, col), value).is_none());
        }
    }
    entries
}

fn kp_in_defect_window(cell: (usize, usize), boundary: usize, row: usize) -> bool {
    let (cell_row, cell_col) = cell;
    cell_col >= boundary.saturating_sub(1)
        && cell_col <= boundary + 4
        && cell_row.abs_diff(row) <= 2
}

fn kp_first_invalid_recording_boundary(columns: &[Vec<usize>]) -> Option<(usize, usize)> {
    for boundary in 0..columns.len().saturating_sub(1) {
        if columns[boundary].len() < columns[boundary + 1].len() {
            return Some((boundary, columns[boundary].len()));
        }
    }
    if !kp_has_partition_shape(columns) {
        return None;
    }
    let rows = kp_columns_to_rows(columns);
    for (row, entries) in rows.iter().enumerate() {
        if let Some(boundary) = entries.windows(2).position(|pair| pair[0] >= pair[1]) {
            return Some((boundary, row));
        }
    }
    for row in 0..rows.len().saturating_sub(1) {
        if let Some(column) = rows[row]
            .iter()
            .zip(&rows[row + 1])
            .position(|(&upper, &lower)| upper >= lower)
        {
            return Some((column.saturating_sub(1), row));
        }
    }
    None
}

fn kp_uniform_candidate_graph(
    poset: &Poset,
    expected: &BTreeSet<KpTableauKey>,
    sources: &[KpSource],
) -> KpCandidateEdges {
    let mut p_pool: BTreeMap<Vec<usize>, BTreeSet<Vec<Vec<usize>>>> = BTreeMap::new();
    let mut q_pool: BTreeMap<Vec<usize>, BTreeSet<KpRecording>> = BTreeMap::new();
    for key in expected {
        let insertion = kp_insertion_from_key(key);
        let shape: Vec<_> = insertion.p_columns.iter().map(Vec::len).collect();
        p_pool
            .entry(shape.clone())
            .or_default()
            .insert(insertion.p_columns);
        q_pool.entry(shape).or_default().insert(insertion.q_columns);
    }

    let mut replay_excludes_raw = BTreeMap::new();
    let mut edges = BTreeMap::new();
    for (word, raw) in sources {
        let (boundary, row) = kp_first_invalid_boundary(poset, &raw.p_columns)
            .map(|(boundary, row, _)| (boundary, row))
            .or_else(|| kp_first_invalid_recording_boundary(&raw.q_columns))
            .expect("a raw defect has an insertion or recording boundary");
        let source_descent_mask =
            reverse_descent_positions(p_descent_mask(poset, word), word.len());
        let source_entries = kp_cell_entries(&raw.p_columns);
        let source_cells: BTreeSet<_> = source_entries.keys().copied().collect();
        let source_shape: Vec<_> = raw.p_columns.iter().map(Vec::len).collect();
        let mut neighbors = BTreeSet::new();
        for (target_shape, p_tableaux) in &p_pool {
            let target_cells: BTreeSet<_> = target_shape
                .iter()
                .enumerate()
                .flat_map(|(col, &height)| (0..height).map(move |row| (row, col)))
                .collect();
            if source_cells.difference(&target_cells).count() > 1
                || source_cells
                    .symmetric_difference(&target_cells)
                    .any(|&cell| !kp_in_defect_window(cell, boundary, row))
            {
                continue;
            }
            let raw_recording_is_eligible = *target_shape == source_shape
                && kp_is_standard_tableau(&raw.q_columns)
                && kp_recording_descent_mask(&raw.q_columns) == source_descent_mask;
            let recording_candidates: Vec<_> = if raw_recording_is_eligible {
                vec![raw.q_columns.clone()]
            } else {
                q_pool
                    .get(target_shape)
                    .into_iter()
                    .flatten()
                    .filter(|recording| {
                        if kp_recording_descent_mask(recording) != source_descent_mask {
                            return false;
                        }
                        let action = kp_column_cell_action(&raw.q_columns, recording);
                        action.moves.len() <= 2
                            && action.moves.iter().all(|&(from, to)| {
                                kp_in_defect_window(from, boundary, row)
                                    && kp_in_defect_window(to, boundary, row)
                            })
                    })
                    .cloned()
                    .collect()
            };
            if recording_candidates.is_empty() {
                continue;
            }
            for p_columns in p_tableaux {
                let target_entries = kp_cell_entries(p_columns);
                if source_entries.iter().any(|(&cell, value)| {
                    target_entries.get(&cell) != Some(value)
                        && !kp_in_defect_window(cell, boundary, row)
                }) {
                    continue;
                }
                let insertion_with_source_q = KpInsertion {
                    p_columns: p_columns.clone(),
                    q_columns: raw.q_columns.clone(),
                };
                if raw.p_columns != *p_columns
                    && kp_asymmetric_p_knuth_certificate(poset, raw, &insertion_with_source_q, 2, 1)
                        .is_none()
                {
                    continue;
                }
                for q_columns in &recording_candidates {
                    let target = KpInsertion {
                        p_columns: p_columns.clone(),
                        q_columns: q_columns.clone(),
                    };
                    let missing_from_raw_image = *replay_excludes_raw
                        .entry(target.clone())
                        .or_insert_with(|| {
                            !kp_inverse_checked(poset, &target, false).is_some_and(|inverse| {
                                kp_insert(poset, &inverse, false).0 == target
                            })
                        });
                    if missing_from_raw_image {
                        neighbors.insert(target);
                    }
                }
            }
        }
        edges.insert(word.clone(), neighbors);
    }
    edges
}

fn kp_candidate_components(
    source_words: &BTreeSet<Vec<usize>>,
    edges: &KpCandidateEdges,
) -> Vec<(Vec<Vec<usize>>, Vec<KpInsertion>)> {
    let mut reverse: BTreeMap<KpInsertion, BTreeSet<Vec<usize>>> = BTreeMap::new();
    for source in source_words {
        for target in edges.get(source).into_iter().flatten() {
            reverse
                .entry(target.clone())
                .or_default()
                .insert(source.clone());
        }
    }
    let mut unseen = source_words.clone();
    let mut components = Vec::new();
    while let Some(first) = unseen.iter().next().cloned() {
        unseen.remove(&first);
        let mut component_sources = BTreeSet::from([first.clone()]);
        let mut component_targets = BTreeSet::new();
        let mut queue = VecDeque::from([first]);
        while let Some(source) = queue.pop_front() {
            for target in edges.get(&source).into_iter().flatten() {
                if !component_targets.insert(target.clone()) {
                    continue;
                }
                for neighbor in &reverse[target] {
                    if component_sources.insert(neighbor.clone()) {
                        unseen.remove(neighbor);
                        queue.push_back(neighbor.clone());
                    }
                }
            }
        }
        components.push((
            component_sources.into_iter().collect(),
            component_targets.into_iter().collect(),
        ));
    }
    components
}

fn kp_uniform_graph_catalog(poset: &Poset) -> KpUniformGraphCatalog {
    let expected = kp_expected_targets(poset);
    let mut sources = BTreeMap::new();
    let mut occupied = BTreeSet::new();
    let mut valid_p_bad_q_count = 0;
    let mut wrong_raw_descent_count = 0;
    for word in permutations(poset.n()) {
        let (raw, _) = kp_insert(poset, &word, true);
        let valid_p = kp_is_p_tableau(poset, &raw.p_columns);
        let valid_q = kp_is_standard_tableau(&raw.q_columns);
        let valid = valid_p && valid_q && expected.contains(&kp_tableau_key(&raw));
        if !valid {
            valid_p_bad_q_count += usize::from(valid_p && !valid_q);
            wrong_raw_descent_count += usize::from(
                kp_recording_descent_mask(&raw.q_columns)
                    != reverse_descent_positions(p_descent_mask(poset, &word), word.len()),
            );
            sources.insert(word, raw);
        } else {
            assert!(occupied.insert(kp_tableau_key(&raw)));
        }
    }
    let source_list: Vec<_> = sources
        .iter()
        .map(|(word, raw)| (word.clone(), raw.clone()))
        .collect();
    let source_count = source_list.len();
    let edges = kp_uniform_candidate_graph(poset, &expected, &source_list);
    let edge_count = edges.values().map(BTreeSet::len).sum();
    let mut remaining_sources = sources;
    let mut remaining_targets: BTreeSet<_> = expected
        .difference(&occupied)
        .map(kp_insertion_from_key)
        .collect();
    let target_count = remaining_targets.len();
    let mut pairs = Vec::new();
    let mut stage_pair_counts = [0; 3];
    let mut stage_component_counts = [0; 3];
    let mut total_cost_ties = 0;
    let mut profile_ties = 0;
    let mut max_source_component = 0;
    let mut max_target_component = 0;
    for stage in 0..3 {
        let mut stage_edges = BTreeMap::new();
        for (word, raw) in &remaining_sources {
            let targets = edges
                .get(word)
                .into_iter()
                .flatten()
                .filter(|target| {
                    remaining_targets.contains(*target)
                        && match stage {
                            0 => {
                                raw.q_columns == target.q_columns
                                    && raw.p_columns[0].len() == target.p_columns[0].len()
                            }
                            1 => raw.p_columns[0].len() == target.p_columns[0].len(),
                            _ => true,
                        }
                })
                .cloned()
                .collect();
            stage_edges.insert(word.clone(), targets);
        }
        let source_words = remaining_sources.keys().cloned().collect();
        let components = kp_candidate_components(&source_words, &stage_edges);
        let mut used_sources = BTreeSet::new();
        let mut used_targets = BTreeSet::new();
        for (component_source_words, component_targets) in components {
            if component_targets.is_empty() {
                continue;
            }
            stage_component_counts[stage] += 1;
            max_source_component = max_source_component.max(component_source_words.len());
            max_target_component = max_target_component.max(component_targets.len());
            let component_sources: Vec<_> = component_source_words
                .iter()
                .map(|word| (word.clone(), remaining_sources[word].clone()))
                .collect();
            let matching = kp_minimum_movement_edge_matching(
                &component_sources,
                &component_targets,
                &stage_edges,
            );
            total_cost_ties += usize::from(matching.total_optimum_count > 1);
            profile_ties += usize::from(matching.profile_optimum_count > 1);
            stage_pair_counts[stage] += matching.pairs.len();
            for ((word, raw), target) in matching.pairs {
                used_sources.insert(word.clone());
                used_targets.insert(target.clone());
                pairs.push(((word, raw), target));
            }
        }
        remaining_sources.retain(|word, _| !used_sources.contains(word));
        remaining_targets.retain(|target| !used_targets.contains(target));
    }
    let unmatched_sources = remaining_sources.into_iter().collect();
    let unmatched_targets = remaining_targets.into_iter().collect();
    pairs.sort_by(|left, right| left.0 .0.cmp(&right.0 .0));
    KpUniformGraphCatalog {
        pairs,
        source_count,
        edge_count,
        target_count,
        valid_p_bad_q_count,
        wrong_raw_descent_count,
        stage_pair_counts,
        stage_component_counts,
        total_cost_ties,
        profile_ties,
        max_source_component,
        max_target_component,
        unmatched_sources,
        unmatched_targets,
    }
}

fn kp_uniform_forward(
    poset: &Poset,
    word: &[usize],
    catalog: &KpUniformGraphCatalog,
) -> KpInsertion {
    let (raw, _) = kp_insert(poset, word, true);
    if kp_is_p_tableau(poset, &raw.p_columns) && kp_is_standard_tableau(&raw.q_columns) {
        return raw;
    }
    catalog
        .pairs
        .iter()
        .find_map(|((source_word, _), target)| (source_word == word).then(|| target.clone()))
        .expect("every raw defect is matched in the uniform candidate graph")
}

fn kp_uniform_reverse(
    poset: &Poset,
    target: &KpInsertion,
    catalog: &KpUniformGraphCatalog,
) -> Vec<usize> {
    if let Some(word) = kp_inverse_checked(poset, target, false) {
        if kp_insert(poset, &word, false).0 == *target {
            return word;
        }
    }
    catalog
        .pairs
        .iter()
        .find_map(|((word, _), candidate)| (candidate == target).then(|| word.clone()))
        .expect("every corrected target is matched in the uniform candidate graph")
}

fn kp_target_signature(poset: &Poset, insertion: &KpInsertion) -> KpTargetSignature {
    let mut window = Vec::new();
    let mut occupancy = Vec::new();
    for (col, column) in insertion.p_columns.iter().enumerate().take(5) {
        for row in 0..column.len().min(3) {
            occupancy.push((row, col));
            window.push(column[column.len() - 1 - row]);
        }
    }
    let mut comparison_code = 0u128;
    let mut place = 1u128;
    for left in 0..window.len() {
        for right in left + 1..window.len() {
            let relation = if poset.lt(window[left], window[right]) {
                1
            } else if poset.lt(window[right], window[left]) {
                2
            } else {
                0
            };
            comparison_code += place * relation;
            place *= 3;
        }
    }
    KpTargetSignature {
        column_shape: insertion.p_columns.iter().map(Vec::len).collect(),
        window_occupancy: occupancy,
        comparison_code,
        recording: insertion.q_columns.clone(),
    }
}

fn kp_correction_catalog(poset: &Poset) -> KpCorrectionCatalog {
    let components = p_knuth_components(poset);
    let mut component_of = BTreeMap::new();
    for (component_index, component) in components.iter().enumerate() {
        for word in component {
            assert!(component_of.insert(word.clone(), component_index).is_none());
        }
    }

    let expected = kp_expected_targets(poset);
    let mut forward = BTreeMap::new();
    let mut reverse = BTreeMap::new();
    let mut invalid_by_fiber: KpInvalidFiber = BTreeMap::new();
    for word in permutations(poset.n()) {
        let (raw, _) = kp_insert(poset, &word, true);
        if kp_is_p_tableau(poset, &raw.p_columns)
            && kp_is_standard_tableau(&raw.q_columns)
            && expected.contains(&kp_tableau_key(&raw))
        {
            assert!(forward.insert(word.clone(), raw.clone()).is_none());
            assert!(reverse.insert(raw, word).is_none());
        } else {
            let fiber = (
                component_of[&word],
                kp_recording_descent_mask(&raw.q_columns),
            );
            invalid_by_fiber.entry(fiber).or_default().push((word, raw));
        }
    }

    let occupied: BTreeSet<KpTableauKey> = reverse.keys().map(kp_tableau_key).collect();
    let mut missing_by_fiber: BTreeMap<(usize, usize), Vec<KpInsertion>> = BTreeMap::new();
    for key in expected.difference(&occupied) {
        let insertion = kp_insertion_from_key(key);
        let reading_word = kp_insertion_reading_word(&insertion);
        let fiber = (
            component_of[&reading_word],
            standard_tableau_descent_mask(&key.0, &key.2),
        );
        missing_by_fiber.entry(fiber).or_default().push(insertion);
    }
    assert_eq!(
        invalid_by_fiber.keys().collect::<Vec<_>>(),
        missing_by_fiber.keys().collect::<Vec<_>>()
    );

    let mut defects = Vec::new();
    let mut max_defect_fiber = 0;
    let mut ambiguous_defect_fibers = 0;
    let mut first_ambiguous_fiber = None;
    let mut max_residual_fiber = 0;
    let mut ambiguous_residual_fibers = 0;
    let mut first_ambiguous_residual = None;
    let mut max_exact_q_group = 0;
    let mut ambiguous_exact_q_groups = 0;
    let mut first_ambiguous_exact_q = None;
    let mut minimum_movement_groups = 0;
    let mut ambiguous_minimum_movement_groups = 0;
    let mut max_minimum_movement_optima = 0;
    let mut first_ambiguous_minimum_movement = None;
    let mut ambiguous_movement_profile_groups = 0;
    let mut max_movement_profile_optima = 0;
    let mut first_ambiguous_movement_profile = None;
    let mut max_exact_height_group = 0;
    let mut ambiguous_exact_height_groups = 0;
    let mut ambiguous_height_movement_groups = 0;
    let mut ambiguous_height_profile_groups = 0;
    let mut max_height_profile_optima = 0;
    let mut first_ambiguous_height_profile = None;
    for (fiber, mut invalid) in invalid_by_fiber {
        let mut missing = missing_by_fiber.remove(&fiber).unwrap();
        invalid.sort_by(|left, right| left.0.cmp(&right.0));
        missing.sort();
        assert_eq!(invalid.len(), missing.len());
        max_defect_fiber = max_defect_fiber.max(invalid.len());
        ambiguous_defect_fibers += usize::from(invalid.len() > 1);
        if invalid.len() > 1 && first_ambiguous_fiber.is_none() {
            first_ambiguous_fiber = Some(KpAmbiguousFiber {
                recording_descent_mask: fiber.1,
                sources: invalid.clone(),
                targets: missing.clone(),
            });
        }
        let mut invalid_by_q: KpInvalidByRecording = BTreeMap::new();
        for source in invalid {
            invalid_by_q
                .entry((source.1.q_columns.clone(), source.1.p_columns[0].len()))
                .or_default()
                .push(source);
        }
        let mut missing_by_q: BTreeMap<KpRecordingHeight, Vec<KpInsertion>> = BTreeMap::new();
        for target in missing {
            missing_by_q
                .entry((target.q_columns.clone(), target.p_columns[0].len()))
                .or_default()
                .push(target);
        }
        let q_keys: BTreeSet<KpRecordingHeight> = invalid_by_q
            .keys()
            .chain(missing_by_q.keys())
            .cloned()
            .collect();
        let mut pairs = Vec::new();
        let mut residual_invalid = Vec::new();
        let mut residual_missing = Vec::new();
        for q in q_keys {
            let mut sources = invalid_by_q.remove(&q).unwrap_or_default();
            let mut targets = missing_by_q.remove(&q).unwrap_or_default();
            sources.sort_by(|left, right| left.0.cmp(&right.0));
            targets.sort();
            let common = sources.len().min(targets.len());
            max_exact_q_group = max_exact_q_group.max(common);
            ambiguous_exact_q_groups += usize::from(common > 1);
            if common > 1 && first_ambiguous_exact_q.is_none() {
                first_ambiguous_exact_q = Some(KpAmbiguousFiber {
                    recording_descent_mask: fiber.1,
                    sources: sources[..common].to_vec(),
                    targets: targets[..common].to_vec(),
                });
            }
            if common > 0 {
                let matching = kp_minimum_movement_matching(&sources, &targets);
                minimum_movement_groups += usize::from(common > 1);
                let optimum_count = matching.total_optimum_count;
                let profile_optimum_count = matching.profile_optimum_count;
                max_minimum_movement_optima = max_minimum_movement_optima.max(optimum_count);
                ambiguous_minimum_movement_groups += usize::from(optimum_count > 1);
                if optimum_count > 1 && first_ambiguous_minimum_movement.is_none() {
                    first_ambiguous_minimum_movement = Some(KpAmbiguousFiber {
                        recording_descent_mask: fiber.1,
                        sources: sources.clone(),
                        targets: targets.clone(),
                    });
                }
                max_movement_profile_optima =
                    max_movement_profile_optima.max(profile_optimum_count);
                ambiguous_movement_profile_groups += usize::from(profile_optimum_count > 1);
                if profile_optimum_count > 1 && first_ambiguous_movement_profile.is_none() {
                    first_ambiguous_movement_profile = Some(KpAmbiguousFiber {
                        recording_descent_mask: fiber.1,
                        sources: sources.clone(),
                        targets: targets.clone(),
                    });
                }
                pairs.extend(matching.pairs);
                sources = matching.residual_sources;
                targets = matching.residual_targets;
            }
            residual_invalid.extend(sources);
            residual_missing.extend(targets);
        }
        residual_invalid.sort_by(|left, right| left.0.cmp(&right.0));
        residual_missing.sort();
        assert_eq!(residual_invalid.len(), residual_missing.len());
        let mut invalid_by_height: BTreeMap<usize, Vec<(Vec<usize>, KpInsertion)>> =
            BTreeMap::new();
        for source in residual_invalid {
            invalid_by_height
                .entry(source.1.p_columns[0].len())
                .or_default()
                .push(source);
        }
        let mut missing_by_height: BTreeMap<usize, Vec<KpInsertion>> = BTreeMap::new();
        for target in residual_missing {
            missing_by_height
                .entry(target.p_columns[0].len())
                .or_default()
                .push(target);
        }
        let heights: BTreeSet<usize> = invalid_by_height
            .keys()
            .chain(missing_by_height.keys())
            .copied()
            .collect();
        let mut final_invalid = Vec::new();
        let mut final_missing = Vec::new();
        for height in heights {
            let mut sources = invalid_by_height.remove(&height).unwrap_or_default();
            let mut targets = missing_by_height.remove(&height).unwrap_or_default();
            sources.sort_by(|left, right| left.0.cmp(&right.0));
            targets.sort();
            let common = sources.len().min(targets.len());
            max_exact_height_group = max_exact_height_group.max(common);
            ambiguous_exact_height_groups += usize::from(common > 1);
            if common > 0 {
                let matching = kp_minimum_movement_matching(&sources, &targets);
                ambiguous_height_movement_groups += usize::from(matching.total_optimum_count > 1);
                ambiguous_height_profile_groups += usize::from(matching.profile_optimum_count > 1);
                max_height_profile_optima =
                    max_height_profile_optima.max(matching.profile_optimum_count);
                if matching.profile_optimum_count > 1 && first_ambiguous_height_profile.is_none() {
                    first_ambiguous_height_profile = Some(KpAmbiguousFiber {
                        recording_descent_mask: fiber.1,
                        sources: sources.clone(),
                        targets: targets.clone(),
                    });
                }
                pairs.extend(matching.pairs);
                sources = matching.residual_sources;
                targets = matching.residual_targets;
            }
            final_invalid.extend(sources);
            final_missing.extend(targets);
        }
        final_invalid.sort_by(|left, right| left.0.cmp(&right.0));
        final_missing.sort();
        assert_eq!(final_invalid.len(), final_missing.len());
        max_residual_fiber = max_residual_fiber.max(final_invalid.len());
        ambiguous_residual_fibers += usize::from(final_invalid.len() > 1);
        if final_invalid.len() > 1 && first_ambiguous_residual.is_none() {
            first_ambiguous_residual = Some(KpAmbiguousFiber {
                recording_descent_mask: fiber.1,
                sources: final_invalid.clone(),
                targets: final_missing.clone(),
            });
        }
        if !final_invalid.is_empty() {
            let matching = kp_minimum_movement_matching(&final_invalid, &final_missing);
            assert!(matching.residual_sources.is_empty());
            assert!(matching.residual_targets.is_empty());
            pairs.extend(matching.pairs);
        }
        for ((word, raw), target) in pairs {
            assert!(kp_is_p_tableau(poset, &target.p_columns));
            assert!(kp_is_standard_tableau(&target.q_columns));
            assert!(forward.insert(word.clone(), target.clone()).is_none());
            assert!(reverse.insert(target.clone(), word.clone()).is_none());
            defects.push((word, raw, target));
        }
    }
    let factorial: usize = (1..=poset.n()).product();
    assert_eq!(forward.len(), factorial);
    assert_eq!(reverse.len(), factorial);
    assert_eq!(
        reverse.keys().map(kp_tableau_key).collect::<BTreeSet<_>>(),
        expected
    );
    defects.sort_by(|left, right| left.0.cmp(&right.0));
    KpCorrectionCatalog {
        forward,
        reverse,
        defects,
        max_defect_fiber,
        ambiguous_defect_fibers,
        first_ambiguous_fiber,
        max_residual_fiber,
        ambiguous_residual_fibers,
        first_ambiguous_residual,
        max_exact_q_group,
        ambiguous_exact_q_groups,
        first_ambiguous_exact_q,
        minimum_movement_groups,
        ambiguous_minimum_movement_groups,
        max_minimum_movement_optima,
        first_ambiguous_minimum_movement,
        ambiguous_movement_profile_groups,
        max_movement_profile_optima,
        first_ambiguous_movement_profile,
        max_exact_height_group,
        ambiguous_exact_height_groups,
        ambiguous_height_movement_groups,
        ambiguous_height_profile_groups,
        max_height_profile_optima,
        first_ambiguous_height_profile,
    }
}

fn verify_kp_insertion_n(n: usize) -> KpCensus {
    let mut summary = KpCensus::default();
    for poset in natural_unit_interval_orders(n) {
        summary.posets += 1;
        summary.ineligible_posets += usize::from(!is_kim_pylyavskyy_eligible(&poset));
        let expected = kp_expected_targets(&poset);
        let mut images = BTreeMap::new();
        let mut poset_defective = false;
        for word in permutations(n) {
            summary.words += 1;
            let (raw, _) = kp_insert(&poset, &word, false);
            let raw_p_valid = kp_is_p_tableau(&poset, &raw.p_columns);
            let raw_q_valid = kp_is_standard_tableau(&raw.q_columns);
            summary.raw_invalid_p += usize::from(!raw_p_valid);
            summary.raw_invalid_q += usize::from(!raw_q_valid);
            let (corrected, trace) = kp_insert(&poset, &word, true);
            summary.repaired_words += usize::from(trace.repaired_rank_five_climber);
            summary.trace_checksum = summary
                .trace_checksum
                .wrapping_add(kp_trace_checksum(&trace));
            let corrected_p_valid = kp_is_p_tableau(&poset, &corrected.p_columns);
            summary.corrected_invalid_p += usize::from(!corrected_p_valid);
            if !corrected_p_valid {
                poset_defective = true;
                if summary.first_defect.is_none() {
                    summary.first_defect = Some(KpDefectWitness {
                        code: poset.code(),
                        word: word.clone(),
                        insertion: corrected.clone(),
                    });
                }
            }
            assert!(kp_is_standard_tableau(&corrected.q_columns));
            assert_eq!(kp_inverse(&poset, &corrected, true), word);
            if images.insert(kp_tableau_key(&corrected), word).is_some() {
                summary.corrected_collisions += 1;
            }
        }
        summary.defective_posets += usize::from(poset_defective);
        let valid_images: BTreeSet<_> = images
            .keys()
            .filter(|key| expected.contains(*key))
            .cloned()
            .collect();
        summary.corrected_missing_targets += expected.difference(&valid_images).count();
        if n <= 5 {
            assert_eq!(images.keys().cloned().collect::<BTreeSet<_>>(), expected);
        }
    }
    summary
}

fn verify_kp_raw_n(n: usize) -> KpRawCensus {
    let mut summary = KpRawCensus::default();
    for poset in natural_unit_interval_orders(n) {
        summary.posets += 1;
        summary.ineligible_posets += usize::from(!is_kim_pylyavskyy_eligible(&poset));
        let mut images = BTreeSet::new();
        let mut poset_defective = false;
        for word in permutations(n) {
            summary.words += 1;
            let (raw, _) = kp_insert(&poset, &word, false);
            let p_shape: Vec<usize> = raw.p_columns.iter().map(Vec::len).collect();
            let q_shape: Vec<usize> = raw.q_columns.iter().map(Vec::len).collect();
            assert_eq!(p_shape, q_shape);
            let p_partition = kp_has_partition_shape(&raw.p_columns);
            let q_partition = kp_has_partition_shape(&raw.q_columns);
            summary.nonpartition_p += usize::from(!p_partition);
            summary.nonpartition_q += usize::from(!q_partition);
            let p_valid = kp_is_p_tableau(&poset, &raw.p_columns);
            let q_valid = kp_is_standard_tableau(&raw.q_columns);
            summary.invalid_p += usize::from(!p_valid);
            summary.invalid_q += usize::from(!q_valid);
            if !p_valid || !q_valid {
                poset_defective = true;
                *summary.shape_compositions.entry(p_shape).or_default() += 1;
                if summary.first_defect.is_none() {
                    summary.first_defect = Some(KpDefectWitness {
                        code: poset.code(),
                        word: word.clone(),
                        insertion: raw.clone(),
                    });
                }
            }
            summary.collisions += usize::from(!images.insert(raw));
        }
        summary.defective_posets += usize::from(poset_defective);
    }
    summary
}

fn p_knuth_neighbors(poset: &Poset, word: &[usize]) -> Vec<Vec<usize>> {
    let mut neighbors = BTreeSet::new();
    for center in 1..word.len().saturating_sub(1) {
        let current = [word[center - 1], word[center], word[center + 1]];
        let mut local = BTreeSet::new();
        for &a in &current {
            for &b in &current {
                for &c in &current {
                    if a == b || a == c || b == c {
                        continue;
                    }
                    let incomparable =
                        |left, right| !poset.lt(left, right) && !poset.lt(right, left);
                    let weak_forward = |left, right| !poset.lt(right, left);
                    let candidates = [
                        (
                            poset.lt(a, b) && weak_forward(b, c) && poset.lt(a, c),
                            [b, a, c],
                            [b, c, a],
                        ),
                        (
                            weak_forward(a, b) && poset.lt(b, c) && poset.lt(a, c),
                            [c, a, b],
                            [a, c, b],
                        ),
                        (
                            incomparable(a, b) && incomparable(b, c) && poset.lt(a, c),
                            [c, a, b],
                            [b, c, a],
                        ),
                    ];
                    for (valid, left, right) in candidates {
                        if !valid {
                            continue;
                        }
                        if current == left {
                            local.insert(right);
                        } else if current == right {
                            local.insert(left);
                        }
                    }
                }
            }
        }
        assert!(local.len() <= 1, "P-Knuth edge color is not an involution");
        for replacement in local {
            let mut neighbor = word.to_vec();
            neighbor[center - 1..=center + 1].copy_from_slice(&replacement);
            neighbors.insert(neighbor);
        }
    }
    neighbors.into_iter().collect()
}

fn p_knuth_components(poset: &Poset) -> Vec<Vec<Vec<usize>>> {
    let all = permutations(poset.n());
    let mut unseen: BTreeSet<Vec<usize>> = all.into_iter().collect();
    let mut components = Vec::new();
    while let Some(start) = unseen.iter().next().cloned() {
        unseen.remove(&start);
        let mut stack = vec![start];
        let mut component = Vec::new();
        while let Some(word) = stack.pop() {
            for neighbor in p_knuth_neighbors(poset, &word) {
                if unseen.remove(&neighbor) {
                    stack.push(neighbor);
                }
            }
            component.push(word);
        }
        component.sort();
        components.push(component);
    }
    components.sort();
    components
}

#[derive(Clone, Debug)]
struct PKnuthComponentWitness {
    code: Vec<usize>,
    size: usize,
    inversion: usize,
    anchor_shapes: BTreeMap<Vec<usize>, usize>,
    first_word: Vec<usize>,
}

#[derive(Default)]
struct PKnuthSummary {
    posets: usize,
    components: usize,
    anchors: usize,
    anchor_excess: usize,
    multi_anchor_components: usize,
    multi_shape_components: usize,
    first_multi_anchor: Option<PKnuthComponentWitness>,
    forbidden_component: Option<PKnuthComponentWitness>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct DirectStandardImage {
    /// The Blasiak--Eriksson--Pylyavskyy--Siegl shape, conjugate to the
    /// Shareshian--Wachs shape stored by `t`.
    p_shape: Vec<usize>,
    /// A Shareshian--Wachs P-tableau, stored as the row of each vertex.
    t: Vec<usize>,
    /// An ordinary standard tableau of shape `p_shape`, stored row by row.
    q: Vec<usize>,
}

struct DirectStandardCatalog {
    forward: BTreeMap<Vec<usize>, DirectStandardImage>,
    reverse: BTreeMap<DirectStandardImage, Vec<usize>>,
}

fn direct_standard_catalog(poset: &Poset) -> DirectStandardCatalog {
    let n = poset.n();
    let mut anchors: BTreeMap<Vec<usize>, (Vec<usize>, Vec<usize>)> = BTreeMap::new();
    for lambda in partitions(n) {
        let p_shape = conjugate_partition(&lambda);
        for tableau in p_tableaux(poset, &lambda) {
            let word = p_tableau_column_word(&tableau);
            assert!(anchors.insert(word, (p_shape.clone(), tableau)).is_none());
        }
    }

    let mut forward = BTreeMap::new();
    let mut reverse = BTreeMap::new();
    for component in p_knuth_components(poset) {
        let component_set: BTreeSet<Vec<usize>> = component.iter().cloned().collect();
        let mut words_by_descent: BTreeMap<usize, Vec<Vec<usize>>> = BTreeMap::new();
        for word in component {
            words_by_descent
                .entry(p_descent_mask(poset, &word))
                .or_default()
                .push(word);
        }
        let mut images_by_descent: BTreeMap<usize, Vec<DirectStandardImage>> = BTreeMap::new();
        for (anchor_word, (p_shape, tableau)) in &anchors {
            if !component_set.contains(anchor_word) {
                continue;
            }
            for standard in ssyts(p_shape, &vec![1; n]) {
                images_by_descent
                    .entry(standard_tableau_descent_mask(p_shape, &standard))
                    .or_default()
                    .push(DirectStandardImage {
                        p_shape: p_shape.clone(),
                        t: tableau.clone(),
                        q: standard,
                    });
            }
        }
        assert_eq!(
            words_by_descent.keys().collect::<Vec<_>>(),
            images_by_descent.keys().collect::<Vec<_>>()
        );
        for (descent, mut words) in words_by_descent {
            let mut images = images_by_descent.remove(&descent).unwrap();
            words.sort();
            images.sort();
            assert_eq!(words.len(), images.len());
            for (word, image) in words.into_iter().zip(images) {
                assert!(forward.insert(word.clone(), image.clone()).is_none());
                assert!(reverse.insert(image, word).is_none());
            }
        }
    }
    let permutation_count: usize = (1..=n).product();
    assert_eq!(forward.len(), permutation_count);
    assert_eq!(reverse.len(), permutation_count);
    DirectStandardCatalog { forward, reverse }
}

fn kp_insertion_direct_image(
    poset: &Poset,
    word: &[usize],
    insertion: &KpInsertion,
) -> DirectStandardImage {
    let (p_shape, p_entries, recording) = kp_tableau_key(insertion);
    let q = evacuate_standard_tableau(&p_shape, &recording);
    assert_eq!(
        p_descent_mask(poset, word),
        standard_tableau_descent_mask(&p_shape, &q),
        "KP recording convention mismatch: P={:?}, word={word:?}, shape={p_shape:?}, raw={recording:?}, transformed={q:?}",
        poset.code()
    );
    let (lambda, transposed_entries) = transpose_tableau(&p_shape, &p_entries);
    let mut t = vec![usize::MAX; poset.n()];
    for (&entry, &(row, _)) in transposed_entries
        .iter()
        .zip(cell_coordinates(&lambda).iter())
    {
        t[entry] = row;
    }
    assert!(t.iter().all(|&row| row != usize::MAX));
    assert_eq!(shape(&t, lambda.len()), lambda);
    assert_eq!(p_word_inversion(poset, word), inv_g(poset, &t));
    DirectStandardImage { p_shape, t, q }
}

fn kp_direct_standard_catalog(poset: &Poset) -> DirectStandardCatalog {
    let insertion_pairs: Vec<_> = if poset.n() == 7 {
        let uniform = kp_uniform_graph_catalog(poset);
        permutations(poset.n())
            .into_iter()
            .map(|word| {
                let insertion = kp_uniform_forward(poset, &word, &uniform);
                (word, insertion)
            })
            .collect()
    } else {
        kp_correction_catalog(poset).forward.into_iter().collect()
    };
    let mut forward = BTreeMap::new();
    let mut reverse = BTreeMap::new();
    for (word, insertion) in insertion_pairs {
        let image = kp_insertion_direct_image(poset, &word, &insertion);
        assert!(forward.insert(word.clone(), image.clone()).is_none());
        assert!(reverse.insert(image, word).is_none());
    }
    let factorial: usize = (1..=poset.n()).product();
    assert_eq!(forward.len(), factorial);
    assert_eq!(reverse.len(), factorial);
    DirectStandardCatalog { forward, reverse }
}

struct KpGarsiaMilneCatalog {
    standard: DirectStandardCatalog,
    raw_good_words: usize,
    corrected_words: usize,
    max_alternating_steps: usize,
}

fn kp_garsia_milne_reverse_trace(
    base: &DirectStandardCatalog,
    raw_good_forward: &BTreeMap<Vec<usize>, DirectStandardImage>,
    endpoint: &DirectStandardImage,
) -> (Vec<usize>, usize) {
    let mut current = base.reverse[endpoint].clone();
    let mut steps = 1;
    while let Some(previous_target) = raw_good_forward.get(&current) {
        current = base.reverse[previous_target].clone();
        steps += 1;
    }
    (current, steps)
}

fn kp_garsia_milne_catalog(poset: &Poset) -> KpGarsiaMilneCatalog {
    let base = direct_standard_catalog(poset);
    let mut raw_good_forward = BTreeMap::new();
    let mut raw_good_owner = BTreeMap::new();
    let mut bad_words = Vec::new();
    for word in permutations(poset.n()) {
        let (raw, _) = kp_insert(poset, &word, false);
        if kp_is_p_tableau(poset, &raw.p_columns) && kp_is_standard_tableau(&raw.q_columns) {
            let image = kp_insertion_direct_image(poset, &word, &raw);
            assert!(base.reverse.contains_key(&image));
            assert!(raw_good_forward
                .insert(word.clone(), image.clone())
                .is_none());
            assert!(raw_good_owner.insert(image, word).is_none());
        } else {
            bad_words.push(word);
        }
    }

    let raw_good_words = raw_good_forward.len();
    let corrected_words = bad_words.len();
    let mut forward = raw_good_forward.clone();
    let mut reverse = raw_good_owner.clone();
    let mut max_alternating_steps = 0;
    for source in bad_words {
        let mut current = source.clone();
        let mut seen = BTreeSet::from([current.clone()]);
        let mut steps = 0;
        loop {
            let target = base.forward[&current].clone();
            steps += 1;
            if let Some(next) = raw_good_owner.get(&target) {
                current = next.clone();
                assert!(
                    seen.insert(current.clone()),
                    "alternating path must terminate"
                );
                continue;
            }
            let (recovered, reverse_steps) =
                kp_garsia_milne_reverse_trace(&base, &raw_good_forward, &target);
            assert_eq!(recovered, source);
            assert_eq!(reverse_steps, steps);
            assert!(forward.insert(source.clone(), target.clone()).is_none());
            assert!(reverse.insert(target, source.clone()).is_none());
            max_alternating_steps = max_alternating_steps.max(steps);
            break;
        }
    }
    let factorial: usize = (1..=poset.n()).product();
    assert_eq!(forward.len(), factorial);
    assert_eq!(reverse.len(), factorial);
    KpGarsiaMilneCatalog {
        standard: DirectStandardCatalog { forward, reverse },
        raw_good_words,
        corrected_words,
        max_alternating_steps,
    }
}

fn transpose_tableau(lambda: &[usize], entries: &[usize]) -> (Vec<usize>, Vec<usize>) {
    assert_eq!(lambda.iter().sum::<usize>(), entries.len());
    let conjugate = conjugate_partition(lambda);
    let mut offsets = Vec::with_capacity(lambda.len());
    let mut offset = 0;
    for &length in lambda {
        offsets.push(offset);
        offset += length;
    }
    let mut transposed = Vec::with_capacity(entries.len());
    for col in 0..conjugate.len() {
        for row in 0..conjugate[col] {
            transposed.push(entries[offsets[row] + col]);
        }
    }
    (conjugate, transposed)
}

fn evacuate_standard_tableau(lambda: &[usize], entries: &[usize]) -> Vec<usize> {
    assert_eq!(lambda.iter().sum::<usize>(), entries.len());
    assert_eq!(
        entries.iter().copied().collect::<BTreeSet<_>>().len(),
        entries.len()
    );
    let mut current = entries_to_rows(lambda, entries, false);
    let mut evacuated = vec![usize::MAX; entries.len()];
    for next in (0..entries.len()).rev() {
        assert_eq!(current[0][0], 0);
        let (mut row, mut col) = (0, 0);
        loop {
            let right = (col + 1 < current[row].len()).then(|| (row, col + 1));
            let below =
                (row + 1 < current.len() && col < current[row + 1].len()).then(|| (row + 1, col));
            let source = match (right, below) {
                (Some(right), Some(below)) => {
                    if current[right.0][right.1] < current[below.0][below.1] {
                        right
                    } else {
                        below
                    }
                }
                (Some(right), None) => right,
                (None, Some(below)) => below,
                (None, None) => break,
            };
            current[row][col] = current[source.0][source.1];
            (row, col) = source;
        }
        assert_eq!(col + 1, current[row].len());
        current[row].pop();
        if current[row].is_empty() {
            assert_eq!(row + 1, current.len());
            current.pop();
        }
        let original_index = lambda[..row].iter().sum::<usize>() + col;
        evacuated[original_index] = next;
        for value in current.iter_mut().flatten() {
            *value -= 1;
        }
    }
    assert!(evacuated.iter().all(|&entry| entry != usize::MAX));
    evacuated
}

fn block_word(poset: &Poset, coloring: &[usize], alphabet: usize) -> Vec<usize> {
    let mut word = Vec::with_capacity(poset.n());
    for color in 0..alphabet {
        let mut chain: Vec<usize> = coloring
            .iter()
            .enumerate()
            .filter_map(|(vertex, &entry)| (entry == color).then_some(vertex))
            .collect();
        chain.reverse();
        assert!(chain.windows(2).all(|pair| poset.lt(pair[1], pair[0])));
        word.extend(chain);
    }
    assert_eq!(word.len(), poset.n());
    word
}

fn coloring_from_block_word(poset: &Poset, word: &[usize], content: &[usize]) -> Vec<usize> {
    assert_eq!(content.iter().sum::<usize>(), poset.n());
    let mut coloring = vec![usize::MAX; poset.n()];
    let mut offset = 0;
    for (color, &length) in content.iter().enumerate() {
        let chain = &word[offset..offset + length];
        assert!(
            chain.windows(2).all(|pair| poset.lt(pair[1], pair[0])),
            "nonchain block in direct inverse: P={:?}, word={word:?}, content={content:?}, color={color}",
            poset.code()
        );
        for &vertex in chain {
            assert_eq!(coloring[vertex], usize::MAX);
            coloring[vertex] = color;
        }
        offset += length;
    }
    assert!(coloring.iter().all(|&color| color != usize::MAX));
    coloring
}

fn destandardize_tableau(entries: &[usize], content: &[usize]) -> Vec<usize> {
    let mut color_of_label = Vec::with_capacity(entries.len());
    for (color, &multiplicity) in content.iter().enumerate() {
        color_of_label.extend(std::iter::repeat_n(color, multiplicity));
    }
    assert_eq!(color_of_label.len(), entries.len());
    entries.iter().map(|&entry| color_of_label[entry]).collect()
}

fn standardize_semistandard_tableau(lambda: &[usize], entries: &[usize]) -> Vec<usize> {
    let coordinates = cell_coordinates(lambda);
    assert_eq!(coordinates.len(), entries.len());
    let alphabet = 1 + *entries.iter().max().expect("a tableau is nonempty");
    let mut standardized = vec![0; entries.len()];
    let mut next_label = 0;
    for color in 0..alphabet {
        let mut positions: Vec<usize> = entries
            .iter()
            .enumerate()
            .filter_map(|(position, &entry)| (entry == color).then_some(position))
            .collect();
        positions.sort_by_key(|&position| {
            let (row, col) = coordinates[position];
            (col, std::cmp::Reverse(row))
        });
        for position in positions {
            standardized[position] = next_label;
            next_label += 1;
        }
    }
    standardized
}

fn tableau_lusztig_involution(lambda: &[usize], entries: &[usize], alphabet: usize) -> Vec<usize> {
    let mut result = entries.to_vec();
    // The semistandard Schuetzenberger--Lusztig involution is the triangular
    // Bender--Knuth word t_1 (t_2 t_1) ... (t_{k-1} ... t_1).  This is not
    // interchangeable with an arbitrary reduced word for the longest
    // permutation: Bender--Knuth involutions do not satisfy the braid
    // relations on semistandard tableaux.
    for largest in 1..alphabet {
        for color in (0..largest).rev() {
            result = bender_knuth(lambda, &result, color);
        }
    }
    result
}

fn direct_forward_with_catalog(
    poset: &Poset,
    coloring: &[usize],
    alphabet: usize,
    catalog: &DirectStandardCatalog,
) -> Target {
    assert!(coloring.iter().all(|&color| color < alphabet));
    assert!(is_proper_coloring(poset, coloring));
    let content = shape(coloring, alphabet);
    let complemented: Vec<usize> = coloring.iter().map(|&color| alphabet - 1 - color).collect();
    let word = block_word(poset, &complemented, alphabet);
    let image = catalog.forward.get(&word).unwrap();
    assert_eq!(
        p_descent_mask(poset, &word),
        standard_tableau_descent_mask(&image.p_shape, &image.q)
    );
    let (lambda, standard_q) = transpose_tableau(&image.p_shape, &image.q);
    assert_eq!(shape(&image.t, lambda.len()), lambda);
    let complemented_content = shape(&complemented, alphabet);
    let q_prime = destandardize_tableau(&standard_q, &complemented_content);
    assert!(is_semistandard_rows(&entries_to_rows(
        &lambda, &q_prime, true
    )));
    let q = tableau_lusztig_involution(&lambda, &q_prime, alphabet);
    assert_eq!(shape(&q, alphabet), content);
    assert_eq!(tableau_lusztig_involution(&lambda, &q, alphabet), q_prime);
    assert_eq!(p_word_inversion(poset, &word), des(poset, &complemented));
    assert_eq!(p_word_inversion(poset, &word), inv_g(poset, &image.t));
    assert_eq!(asc(poset, coloring), inv_g(poset, &image.t));
    Target {
        lambda,
        t: image.t.clone(),
        q,
    }
}

fn direct_reverse_with_catalog(
    poset: &Poset,
    target: &Target,
    content: &[usize],
    catalog: &DirectStandardCatalog,
) -> Vec<usize> {
    assert_eq!(shape(&target.q, content.len()), content);
    let q_prime = tableau_lusztig_involution(&target.lambda, &target.q, content.len());
    let standard_q = standardize_semistandard_tableau(&target.lambda, &q_prime);
    let (p_shape, q) = transpose_tableau(&target.lambda, &standard_q);
    let image = DirectStandardImage {
        p_shape,
        t: target.t.clone(),
        q,
    };
    let word = catalog.reverse.get(&image).unwrap();
    let mut complemented_content = content.to_vec();
    complemented_content.reverse();
    let complemented = coloring_from_block_word(poset, word, &complemented_content);
    let coloring: Vec<usize> = complemented
        .iter()
        .map(|&color| content.len() - 1 - color)
        .collect();
    assert!(is_proper_coloring(poset, &coloring));
    assert_eq!(shape(&coloring, content.len()), content);
    coloring
}

fn direct_coloring_crystal_operator(
    poset: &Poset,
    coloring: &[usize],
    alphabet: usize,
    color: usize,
    raising: bool,
    catalog: &DirectStandardCatalog,
) -> Option<Vec<usize>> {
    let target = direct_forward_with_catalog(poset, coloring, alphabet, catalog);
    let moved_target = crystal_on_target(&target, color, raising)?;
    let moved_content = shape(&moved_target.q, alphabet);
    Some(direct_reverse_with_catalog(
        poset,
        &moved_target,
        &moved_content,
        catalog,
    ))
}

fn verify_p_knuth_components_n(n: usize) -> PKnuthSummary {
    let mut summary = PKnuthSummary::default();
    for poset in natural_unit_interval_orders(n) {
        summary.posets += 1;
        let mut anchors: BTreeMap<Vec<usize>, Vec<Vec<usize>>> = BTreeMap::new();
        let mut anchor_shapes = BTreeMap::new();
        for lambda in partitions(n) {
            let conjugate = conjugate_partition(&lambda);
            for tableau in p_tableaux(&poset, &lambda) {
                let word = p_tableau_column_word(&tableau);
                assert_eq!(p_word_inversion(&poset, &word), inv_g(&poset, &tableau));
                assert!(anchor_shapes
                    .insert(word.clone(), conjugate.clone())
                    .is_none());
                anchors.entry(word).or_default().push(tableau);
            }
        }
        for component in p_knuth_components(&poset) {
            summary.components += 1;
            let inversion = p_word_inversion(&poset, &component[0]);
            assert!(component
                .iter()
                .all(|word| p_word_inversion(&poset, word) == inversion));
            let component_set: BTreeSet<Vec<usize>> = component.iter().cloned().collect();
            let mut shapes = BTreeMap::new();
            let mut expected_by_descent = BTreeMap::new();
            let mut anchor_count = 0;
            for (word, tableaux) in &anchors {
                if !component_set.contains(word) {
                    continue;
                }
                assert_eq!(tableaux.len(), 1);
                anchor_count += 1;
                let shape = anchor_shapes.get(word).unwrap();
                *shapes.entry(shape.clone()).or_default() += 1;
                for standard in ssyts(shape, &vec![1; n]) {
                    *expected_by_descent
                        .entry(standard_tableau_descent_mask(shape, &standard))
                        .or_default() += 1;
                }
            }
            let mut actual_by_descent = BTreeMap::new();
            for word in &component {
                *actual_by_descent
                    .entry(p_descent_mask(&poset, word))
                    .or_default() += 1;
            }
            assert_eq!(
                actual_by_descent,
                expected_by_descent,
                "P-Knuth Schur inventory mismatch for P={:?}, component={component:?}",
                poset.code()
            );
            assert_eq!(component.len(), expected_by_descent.values().sum());
            summary.anchors += anchor_count;
            summary.anchor_excess += anchor_count.saturating_sub(1);
            let witness = PKnuthComponentWitness {
                code: poset.code(),
                size: component.len(),
                inversion,
                anchor_shapes: shapes.clone(),
                first_word: component[0].clone(),
            };
            if anchor_count > 1 {
                summary.multi_anchor_components += 1;
                if summary.first_multi_anchor.is_none() {
                    summary.first_multi_anchor = Some(witness.clone());
                }
            }
            if shapes.len() > 1 {
                summary.multi_shape_components += 1;
            }
            if poset.code() == vec![2, 4, 4, 5, 5] && component_set.contains(&vec![2, 3, 4, 1, 0]) {
                summary.forbidden_component = Some(witness);
            }
        }
    }
    summary
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

fn forward_loehr_mendes_with_alphabet(
    poset: &Poset,
    coloring: &[usize],
    alphabet: usize,
) -> (Target, Vec<LoehrMendesTraceEvent>) {
    assert!(coloring.iter().all(|&color| color < alphabet));
    let mu = shape(coloring, alphabet);
    let oriented = orient_asc_to_des(poset, coloring, alphabet);
    assert_eq!(shape(&oriented, alphabet), mu);
    assert_eq!(des(poset, &oriented), asc(poset, coloring));
    let mut padded_mu = mu.clone();
    padded_mu.resize(poset.n(), 0);
    let (normalized, _) = normalize(poset, &oriented, &padded_mu);
    assert!(normalized.iter().all(|&row| row < poset.n()));
    let mut state = State {
        a: normalized,
        triple: canonical_fixed_triple(poset.n(), &mu),
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
        trace.push(LoehrMendesTraceEvent::Sw(event));
        state = new_state;
        let nu = decreasing_rearrangement(&shape(&state.a, poset.n()));
        let old = state.triple.clone();
        let (partner, local) = inverse_kostka_loehr_mendes_local(&state.triple, &nu, &mu)
            .expect("negative state cannot be fixed by inverse-Kostka involution");
        state.triple = partner;
        let (reversed, reverse_local) = inverse_kostka_loehr_mendes_local(&state.triple, &nu, &mu)
            .expect("local inverse-Kostka move must reverse itself");
        assert_eq!(reversed, old);
        assert_eq!(reverse_local, reversed_loehr_mendes_events(&local));
        trace.push(LoehrMendesTraceEvent::InverseKostka {
            nu,
            from: old,
            to: state.triple.clone(),
            local,
        });
    }
    panic!("Loehr--Mendes Garsia--Milne forward path exceeded safety bound");
}

fn reverse_loehr_mendes(poset: &Poset, target: &Target, mu: &[usize]) -> Vec<usize> {
    let n = poset.n();
    let mut state = State {
        a: target.t.clone(),
        triple: Triple {
            lambda: target.lambda.clone(),
            pi: (0..n).collect(),
            q: target.q.clone(),
        },
    };
    for _ in 0..100_000 {
        let nu = decreasing_rearrangement(&shape(&state.a, n));
        let Some((partner, _)) = inverse_kostka_loehr_mendes_local(&state.triple, &nu, mu) else {
            let mut padded_mu = mu.to_vec();
            padded_mu.resize(n, 0);
            let oriented = denormalize(poset, &state.a, &padded_mu);
            return undo_asc_to_des(poset, &oriented, mu.len());
        };
        state.triple = partner;
        state = sw_conjugate(poset, &state)
            .expect("nonfixed inverse-Kostka state must move under SW")
            .0;
    }
    panic!("Loehr--Mendes Garsia--Milne reverse path exceeded safety bound");
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

#[derive(Default)]
struct DirectMapSummary {
    posets: usize,
    colorings: usize,
    targets: usize,
    differing_from_signed: usize,
    lowering_edges: usize,
}

fn verify_direct_map_n(n: usize) -> DirectMapSummary {
    let mut summary = DirectMapSummary::default();
    for poset in natural_unit_interval_orders(n) {
        summary.posets += 1;
        let catalog = direct_standard_catalog(&poset);
        let mut by_weight: BTreeMap<Vec<usize>, Vec<Vec<usize>>> = BTreeMap::new();
        for coloring in proper_colorings(&poset, n) {
            by_weight
                .entry(shape(&coloring, n))
                .or_default()
                .push(coloring);
        }
        for (content, sources) in by_weight {
            let expected: BTreeSet<Target> = target_fiber(&poset, &content).into_iter().collect();
            let mut images = BTreeSet::new();
            for source in &sources {
                let image = direct_forward_with_catalog(&poset, source, n, &catalog);
                assert_eq!(shape(&image.q, n), content);
                assert_eq!(asc(&poset, source), inv_g(&poset, &image.t));
                assert_eq!(
                    direct_reverse_with_catalog(&poset, &image, &content, &catalog),
                    *source
                );
                summary.differing_from_signed +=
                    usize::from(forward_with_alphabet(&poset, source, n).0 != image);
                assert!(images.insert(image.clone()));
                for color in 0..n.saturating_sub(1) {
                    let Some(moved) =
                        direct_coloring_crystal_operator(&poset, source, n, color, false, &catalog)
                    else {
                        continue;
                    };
                    let moved_target = crystal_on_target(&image, color, false).unwrap();
                    let moved_content = shape(&moved_target.q, n);
                    assert_eq!(
                        direct_forward_with_catalog(&poset, &moved, n, &catalog),
                        moved_target
                    );
                    assert_eq!(shape(&moved, n), moved_content);
                    assert_eq!(asc(&poset, &moved), asc(&poset, source));
                    assert_eq!(
                        direct_coloring_crystal_operator(&poset, &moved, n, color, true, &catalog,)
                            .as_ref(),
                        Some(source)
                    );
                    summary.lowering_edges += 1;
                }
            }
            assert_eq!(images, expected);
            summary.colorings += sources.len();
            summary.targets += images.len();
        }
    }
    summary
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

fn loehr_mendes_trace_checksum(trace: &[LoehrMendesTraceEvent]) -> usize {
    trace
        .iter()
        .map(|event| match event {
            LoehrMendesTraceEvent::Sw(event) => event.row + event.col + event.normalize_swaps.len(),
            LoehrMendesTraceEvent::InverseKostka {
                nu,
                from,
                to,
                local,
            } => {
                let local_sum: usize = local
                    .iter()
                    .map(|event| match event {
                        LoehrMendesEvent::AdjointSwap {
                            content,
                            used_carrier,
                            parked_old_d,
                        } => {
                            content.iter().sum::<usize>()
                                + usize::from(*used_carrier)
                                + usize::from(*parked_old_d)
                        }
                        LoehrMendesEvent::Er { row, largest } => row + largest,
                        LoehrMendesEvent::CarrierSwap {
                            content,
                            used_carrier,
                            parked_old_b,
                        } => {
                            content.iter().sum::<usize>()
                                + usize::from(*used_carrier)
                                + usize::from(*parked_old_b)
                        }
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

fn verify_loehr_mendes_inverse_kostka_n(n: usize) -> (usize, usize, usize) {
    let mut endpoint_states = 0;
    let mut differing_endpoints = 0;
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
            let fiber: BTreeSet<Triple> = triples.iter().cloned().collect();
            for triple in triples {
                endpoint_states += 1;
                let partner = inverse_kostka_loehr_mendes_local(&triple, &nu, &mu);
                if nu == mu_plus {
                    assert!(partner.is_none());
                    continue;
                }
                let (partner, events) = partner.expect("off-diagonal fiber has no fixed points");
                assert!(fiber.contains(&partner));
                assert_eq!(permutation_sign(&partner.pi), -permutation_sign(&triple.pi));
                let (reversed, reverse_events) =
                    inverse_kostka_loehr_mendes_local(&partner, &nu, &mu)
                        .expect("Loehr--Mendes partner must reverse");
                assert_eq!(reversed, triple);
                assert_eq!(reverse_events, reversed_loehr_mendes_events(&events));
                let acm_partner = inverse_kostka_local(&triple, &nu, &mu)
                    .expect("off-diagonal ACM fiber has no fixed points")
                    .0;
                differing_endpoints += usize::from(partner != acm_partner);
                max_local_events = max_local_events.max(events.len());
            }
        }
    }
    (endpoint_states, differing_endpoints, max_local_events)
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

#[derive(Clone, Debug)]
struct OracleMapDifference {
    code: Vec<usize>,
    source: Vec<usize>,
    acm: Target,
    loehr_mendes: Target,
}

#[derive(Clone, Debug)]
struct OracleOperatorDifference {
    code: Vec<usize>,
    color: usize,
    source: Vec<usize>,
    acm: Option<Vec<usize>>,
    loehr_mendes: Option<Vec<usize>>,
}

#[derive(Default)]
struct OracleComparisonSummary {
    colorings: usize,
    differing_images: usize,
    lowering_tests: usize,
    differing_lowering: usize,
    lowering_definedness_differences: usize,
    lowering_value_differences: usize,
    reflection_tests: usize,
    differing_reflections: usize,
    max_trace_events: usize,
    trace_checksum: usize,
    first_image_difference: Option<OracleMapDifference>,
    first_lowering_difference: Option<OracleOperatorDifference>,
    first_reflection_difference: Option<OracleOperatorDifference>,
}

fn verify_loehr_mendes_coloring_map_n(n: usize) -> OracleComparisonSummary {
    let mut summary = OracleComparisonSummary::default();
    for poset in natural_unit_interval_orders(n) {
        let colorings = proper_colorings(&poset, n);
        let mut records = Vec::with_capacity(colorings.len());
        let mut acm_inverse = BTreeMap::new();
        let mut loehr_mendes_inverse = BTreeMap::new();
        for source in colorings {
            let mu = shape(&source, n);
            let acm = forward_with_alphabet(&poset, &source, n).0;
            let (loehr_mendes, trace) = forward_loehr_mendes_with_alphabet(&poset, &source, n);
            assert_eq!(shape(&loehr_mendes.q, n), mu);
            assert_eq!(asc(&poset, &source), inv_g(&poset, &loehr_mendes.t));
            assert_eq!(reverse_loehr_mendes(&poset, &loehr_mendes, &mu), source);
            assert!(acm_inverse.insert(acm.clone(), source.clone()).is_none());
            assert!(loehr_mendes_inverse
                .insert(loehr_mendes.clone(), source.clone())
                .is_none());
            if acm != loehr_mendes {
                summary.differing_images += 1;
                if summary.first_image_difference.is_none() {
                    summary.first_image_difference = Some(OracleMapDifference {
                        code: poset.code(),
                        source: source.clone(),
                        acm: acm.clone(),
                        loehr_mendes: loehr_mendes.clone(),
                    });
                }
            }
            let event_count: usize = trace
                .iter()
                .map(|event| match event {
                    LoehrMendesTraceEvent::Sw(_) => 1,
                    LoehrMendesTraceEvent::InverseKostka { local, .. } => local.len(),
                })
                .sum();
            summary.max_trace_events = summary.max_trace_events.max(event_count);
            summary.trace_checksum = summary
                .trace_checksum
                .wrapping_add(loehr_mendes_trace_checksum(&trace));
            records.push((source, acm, loehr_mendes));
        }
        assert_eq!(
            acm_inverse.keys().collect::<Vec<_>>(),
            loehr_mendes_inverse.keys().collect::<Vec<_>>(),
            "the two coloring maps must cover the same target set for P={:?}",
            poset.code()
        );

        for (source, acm, loehr_mendes) in records {
            summary.colorings += 1;
            for color in 0..n.saturating_sub(1) {
                let acm_lowered = crystal_on_target(&acm, color, false)
                    .map(|target| acm_inverse.get(&target).unwrap().clone());
                let loehr_mendes_lowered = crystal_on_target(&loehr_mendes, color, false)
                    .map(|target| loehr_mendes_inverse.get(&target).unwrap().clone());
                summary.lowering_tests += 1;
                if acm_lowered != loehr_mendes_lowered {
                    summary.differing_lowering += 1;
                    if acm_lowered.is_some() != loehr_mendes_lowered.is_some() {
                        summary.lowering_definedness_differences += 1;
                    } else {
                        summary.lowering_value_differences += 1;
                    }
                    if summary.first_lowering_difference.is_none() {
                        summary.first_lowering_difference = Some(OracleOperatorDifference {
                            code: poset.code(),
                            color,
                            source: source.clone(),
                            acm: acm_lowered,
                            loehr_mendes: loehr_mendes_lowered,
                        });
                    }
                }

                let acm_reflected = acm_inverse
                    .get(&crystal_reflection_on_target(&acm, n, color))
                    .unwrap()
                    .clone();
                let loehr_mendes_reflected = loehr_mendes_inverse
                    .get(&crystal_reflection_on_target(&loehr_mendes, n, color))
                    .unwrap()
                    .clone();
                summary.reflection_tests += 1;
                if acm_reflected != loehr_mendes_reflected {
                    summary.differing_reflections += 1;
                    if summary.first_reflection_difference.is_none() {
                        summary.first_reflection_difference = Some(OracleOperatorDifference {
                            code: poset.code(),
                            color,
                            source: source.clone(),
                            acm: Some(acm_reflected),
                            loehr_mendes: Some(loehr_mendes_reflected),
                        });
                    }
                }
            }
        }
    }
    summary
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
    if args.get(1).map(String::as_str) == Some("--kp-uniform-code") {
        assert_eq!(args.len(), 3, "usage: --kp-uniform-code h_1,...,h_n");
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
        let catalog = kp_uniform_graph_catalog(&Poset { h });
        println!(
            "KP uniform code={}: sources={}, missing-targets={}, edges={}, matched={}, unmatched-sources={}, unmatched-targets={}, valid-P/bad-Q={}, wrong-raw-descent={}, stages={:?}, components={:?}, total-ties={}, profile-ties={}, max-component={}+{}",
            args[2],
            catalog.source_count,
            catalog.target_count,
            catalog.edge_count,
            catalog.pairs.len(),
            catalog.unmatched_sources.len(),
            catalog.unmatched_targets.len(),
            catalog.valid_p_bad_q_count,
            catalog.wrong_raw_descent_count,
            catalog.stage_pair_counts,
            catalog.stage_component_counts,
            catalog.total_cost_ties,
            catalog.profile_ties,
            catalog.max_source_component,
            catalog.max_target_component,
        );
        if let Some((word, raw)) = catalog.unmatched_sources.first() {
            println!("first unmatched source={word:?}, raw={raw:?}");
        }
        if let Some(target) = catalog.unmatched_targets.first() {
            println!("first unmatched target={target:?}");
        }
        return;
    }
    if args.get(1).map(String::as_str) == Some("--kp-gm") {
        assert_eq!(args.len(), 3, "usage: --kp-gm rank");
        let n = args[2].parse::<usize>().expect("rank must be numeric");
        assert!(n <= 6, "the Garsia--Milne census is bounded to rank six");
        let mut posets = 0;
        let mut targets = 0;
        let mut raw_good_words = 0;
        let mut corrected_words = 0;
        let mut max_alternating_steps = 0;
        for poset in natural_unit_interval_orders(n) {
            let catalog = kp_garsia_milne_catalog(&poset);
            posets += 1;
            targets += catalog.standard.forward.len();
            raw_good_words += catalog.raw_good_words;
            corrected_words += catalog.corrected_words;
            max_alternating_steps = max_alternating_steps.max(catalog.max_alternating_steps);
        }
        println!(
            "KP Garsia--Milne n={n}: posets={posets}, targets={targets}, raw-good={raw_good_words}, corrected={corrected_words}, max-alternating-steps={max_alternating_steps}",
        );
        return;
    }
    if args.get(1).map(String::as_str) == Some("--kp-correct") {
        assert_eq!(args.len(), 3, "usage: --kp-correct rank");
        let n = args[2].parse::<usize>().expect("rank must be numeric");
        assert!(
            n <= 7,
            "the correction census is bounded to rank at most seven"
        );
        let mut defects = 0;
        let mut same_recording = 0;
        let mut shape_changes = 0;
        let mut malformed_sources = 0;
        let mut shape_boundary_cases = 0;
        let mut shape_boundary_failures = 0;
        let mut recording_shape_cases = 0;
        let mut recording_shape_failures = 0;
        let mut recording_shape_unique = 0;
        let mut recording_shape_max_candidates = 0;
        let mut transposition_cases = 0;
        let mut transposition_ties = 0;
        let mut transposition_failures = 0;
        let mut local_p_knuth_certificates = [0usize; 3];
        let mut local_p_knuth_max_distances = [0usize; 3];
        let mut local_p_knuth_max_interval = 0;
        let mut uniform_graph_edges = 0;
        let mut uniform_graph_targets = 0;
        let mut uniform_graph_stage_pairs = [0usize; 3];
        let mut uniform_graph_stage_components = [0usize; 3];
        let mut uniform_graph_total_ties = 0;
        let mut uniform_graph_profile_ties = 0;
        let mut uniform_graph_max_source_component = 0;
        let mut uniform_graph_max_target_component = 0;
        let mut max_defect_fiber = 0;
        let mut ambiguous_defect_fibers = 0;
        let mut max_residual_fiber = 0;
        let mut ambiguous_residual_fibers = 0;
        let mut max_exact_q_group = 0;
        let mut ambiguous_exact_q_groups = 0;
        let mut minimum_movement_groups = 0;
        let mut ambiguous_minimum_movement_groups = 0;
        let mut max_minimum_movement_optima = 0;
        let mut ambiguous_movement_profile_groups = 0;
        let mut max_movement_profile_optima = 0;
        let mut max_exact_height_group = 0;
        let mut ambiguous_exact_height_groups = 0;
        let mut ambiguous_height_movement_groups = 0;
        let mut ambiguous_height_profile_groups = 0;
        let mut max_height_profile_optima = 0;
        let mut p_actions: BTreeMap<KpCellAction, usize> = BTreeMap::new();
        let mut pair_actions: BTreeMap<KpPairAction, usize> = BTreeMap::new();
        let mut source_p_actions: BTreeMap<KpLocalSignature, BTreeSet<KpCellAction>> =
            BTreeMap::new();
        let mut source_pair_actions: BTreeMap<KpLocalSignature, BTreeSet<KpPairAction>> =
            BTreeMap::new();
        let mut target_pair_actions: BTreeMap<KpLocalSignature, BTreeSet<KpPairAction>> =
            BTreeMap::new();
        let mut relation_p_actions: BTreeMap<KpStructuralSignature, BTreeSet<KpCellAction>> =
            BTreeMap::new();
        let mut ordered_p_actions: BTreeMap<KpStructuralSignature, BTreeSet<KpCellAction>> =
            BTreeMap::new();
        let mut recorded_pair_actions: BTreeMap<KpStructuralSignature, BTreeSet<KpPairAction>> =
            BTreeMap::new();
        let mut relation_recorded_pair_actions: BTreeMap<
            KpStructuralSignature,
            BTreeSet<KpPairAction>,
        > = BTreeMap::new();
        let mut trace_pair_actions: BTreeMap<
            (KpStructuralSignature, Vec<Vec<usize>>),
            BTreeSet<KpPairAction>,
        > = BTreeMap::new();
        let mut boundary_pair_actions: BTreeMap<KpBoundarySignature, BTreeSet<KpPairAction>> =
            BTreeMap::new();
        let mut target_signature_data: BTreeMap<
            KpTargetSignature,
            (BTreeSet<KpPairAction>, usize, usize),
        > = BTreeMap::new();
        let mut p_to_q_actions: BTreeMap<KpCellAction, BTreeSet<KpCellAction>> = BTreeMap::new();
        let mut first_ambiguous = None;
        let mut first_ambiguous_residual = None;
        let mut first_ambiguous_exact_q = None;
        let mut first_ambiguous_minimum_movement = None;
        let mut first_ambiguous_movement_profile = None;
        let mut first_ambiguous_height_profile = None;
        for poset in natural_unit_interval_orders(n) {
            let catalog = kp_correction_catalog(&poset);
            if n == 7 && !catalog.defects.is_empty() {
                let uniform = kp_uniform_graph_catalog(&poset);
                let catalog_targets: BTreeMap<_, _> = catalog
                    .defects
                    .iter()
                    .map(|(word, _, target)| (word.clone(), target.clone()))
                    .collect();
                let uniform_targets: BTreeMap<_, _> = uniform
                    .pairs
                    .iter()
                    .map(|((word, _), target)| (word.clone(), target.clone()))
                    .collect();
                assert_eq!(uniform_targets, catalog_targets);
                for (word, target) in &uniform_targets {
                    assert_eq!(kp_uniform_forward(&poset, word, &uniform), *target);
                    assert_eq!(kp_uniform_reverse(&poset, target, &uniform), *word);
                }
                uniform_graph_edges += uniform.edge_count;
                uniform_graph_targets += uniform.target_count;
                for stage in 0..3 {
                    uniform_graph_stage_pairs[stage] += uniform.stage_pair_counts[stage];
                    uniform_graph_stage_components[stage] += uniform.stage_component_counts[stage];
                }
                uniform_graph_total_ties += uniform.total_cost_ties;
                uniform_graph_profile_ties += uniform.profile_ties;
                uniform_graph_max_source_component =
                    uniform_graph_max_source_component.max(uniform.max_source_component);
                uniform_graph_max_target_component =
                    uniform_graph_max_target_component.max(uniform.max_target_component);
            }
            max_defect_fiber = max_defect_fiber.max(catalog.max_defect_fiber);
            ambiguous_defect_fibers += catalog.ambiguous_defect_fibers;
            max_residual_fiber = max_residual_fiber.max(catalog.max_residual_fiber);
            ambiguous_residual_fibers += catalog.ambiguous_residual_fibers;
            max_exact_q_group = max_exact_q_group.max(catalog.max_exact_q_group);
            ambiguous_exact_q_groups += catalog.ambiguous_exact_q_groups;
            minimum_movement_groups += catalog.minimum_movement_groups;
            ambiguous_minimum_movement_groups += catalog.ambiguous_minimum_movement_groups;
            max_minimum_movement_optima =
                max_minimum_movement_optima.max(catalog.max_minimum_movement_optima);
            ambiguous_movement_profile_groups += catalog.ambiguous_movement_profile_groups;
            max_movement_profile_optima =
                max_movement_profile_optima.max(catalog.max_movement_profile_optima);
            max_exact_height_group = max_exact_height_group.max(catalog.max_exact_height_group);
            ambiguous_exact_height_groups += catalog.ambiguous_exact_height_groups;
            ambiguous_height_movement_groups += catalog.ambiguous_height_movement_groups;
            ambiguous_height_profile_groups += catalog.ambiguous_height_profile_groups;
            max_height_profile_optima =
                max_height_profile_optima.max(catalog.max_height_profile_optima);
            if first_ambiguous.is_none() {
                first_ambiguous = catalog
                    .first_ambiguous_fiber
                    .clone()
                    .map(|fiber| (poset.code(), fiber));
            }
            if first_ambiguous_residual.is_none() {
                first_ambiguous_residual = catalog
                    .first_ambiguous_residual
                    .clone()
                    .map(|fiber| (poset.code(), fiber));
            }
            if first_ambiguous_exact_q.is_none() {
                first_ambiguous_exact_q = catalog
                    .first_ambiguous_exact_q
                    .clone()
                    .map(|fiber| (poset.code(), fiber));
            }
            if first_ambiguous_minimum_movement.is_none() {
                first_ambiguous_minimum_movement = catalog
                    .first_ambiguous_minimum_movement
                    .clone()
                    .map(|fiber| (poset.code(), fiber));
            }
            if first_ambiguous_movement_profile.is_none() {
                first_ambiguous_movement_profile = catalog
                    .first_ambiguous_movement_profile
                    .clone()
                    .map(|fiber| (poset.code(), fiber));
            }
            if first_ambiguous_height_profile.is_none() {
                first_ambiguous_height_profile = catalog
                    .first_ambiguous_height_profile
                    .clone()
                    .map(|fiber| (poset.code(), fiber));
            }
            let defect_inverse_by_target: BTreeMap<KpInsertion, KpPairAction> = catalog
                .defects
                .iter()
                .map(|(_, raw, target)| (target.clone(), kp_pair_action(target, raw)))
                .collect();
            for (_, raw, target) in &catalog.defects {
                let certificate = kp_local_p_knuth_certificate(&poset, raw, target, 2)
                    .expect("every selected rank-seven repair has a margin-two certificate");
                local_p_knuth_certificates[certificate.margin] += 1;
                local_p_knuth_max_distances[certificate.margin] =
                    local_p_knuth_max_distances[certificate.margin].max(certificate.distance);
                local_p_knuth_max_interval =
                    local_p_knuth_max_interval.max(certificate.last - certificate.first + 1);
                if raw.q_columns != target.q_columns {
                    recording_shape_cases += 1;
                    let candidates = kp_recording_shape_repair_candidates(raw);
                    recording_shape_failures +=
                        usize::from(!candidates.contains(&target.q_columns));
                    recording_shape_unique += usize::from(candidates.len() == 1);
                    recording_shape_max_candidates =
                        recording_shape_max_candidates.max(candidates.len());
                }
                let repairs = kp_boundary_transposition_repairs(&poset, raw);
                transposition_cases += usize::from(!repairs.is_empty());
                transposition_ties += usize::from(repairs.len() > 1);
                transposition_failures += usize::from(
                    !repairs.is_empty() && (repairs.len() != 1 || repairs[0] != *target),
                );
            }
            for target in catalog.reverse.keys() {
                let data = target_signature_data
                    .entry(kp_target_signature(&poset, target))
                    .or_default();
                if let Some(action) = defect_inverse_by_target.get(target) {
                    data.0.insert(action.clone());
                    data.1 += 1;
                } else {
                    data.2 += 1;
                }
            }
            for (word, raw, target) in catalog.defects {
                defects += 1;
                same_recording += usize::from(raw.q_columns == target.q_columns);
                let raw_shape: Vec<usize> = raw.p_columns.iter().map(Vec::len).collect();
                let target_shape: Vec<usize> = target.p_columns.iter().map(Vec::len).collect();
                shape_changes += usize::from(raw_shape != target_shape);
                malformed_sources += usize::from(!kp_has_partition_shape(&raw.p_columns));
                if let Some(repaired) = kp_shape_boundary_repair(&poset, &raw) {
                    shape_boundary_cases += 1;
                    shape_boundary_failures += usize::from(repaired != target);
                }
                let p_action = kp_cell_action(&raw, &target);
                let pair_action = kp_pair_action(&raw, &target);
                *p_actions.entry(p_action.clone()).or_default() += 1;
                *pair_actions.entry(pair_action.clone()).or_default() += 1;
                source_p_actions
                    .entry(kp_local_signature(&poset, &raw))
                    .or_default()
                    .insert(p_action);
                source_pair_actions
                    .entry(kp_local_signature(&poset, &raw))
                    .or_default()
                    .insert(pair_action);
                relation_p_actions
                    .entry(kp_structural_signature(&poset, &raw, false, false))
                    .or_default()
                    .insert(kp_cell_action(&raw, &target));
                ordered_p_actions
                    .entry(kp_structural_signature(&poset, &raw, true, false))
                    .or_default()
                    .insert(kp_cell_action(&raw, &target));
                recorded_pair_actions
                    .entry(kp_structural_signature(&poset, &raw, true, true))
                    .or_default()
                    .insert(kp_pair_action(&raw, &target));
                relation_recorded_pair_actions
                    .entry(kp_structural_signature(&poset, &raw, false, true))
                    .or_default()
                    .insert(kp_pair_action(&raw, &target));
                let (replayed_raw, trace) = kp_insert(&poset, &word, false);
                assert_eq!(replayed_raw, raw);
                let event_kinds = trace
                    .passes
                    .iter()
                    .map(|pass| {
                        pass.events
                            .iter()
                            .map(|event| event.kind as usize)
                            .collect()
                    })
                    .collect();
                trace_pair_actions
                    .entry((
                        kp_structural_signature(&poset, &raw, false, false),
                        event_kinds,
                    ))
                    .or_default()
                    .insert(kp_pair_action(&raw, &target));
                boundary_pair_actions
                    .entry(kp_boundary_signature(&poset, &raw))
                    .or_default()
                    .insert(kp_pair_action(&raw, &target));
                p_to_q_actions
                    .entry(kp_cell_action(&raw, &target))
                    .or_default()
                    .insert(kp_column_cell_action(&raw.q_columns, &target.q_columns));
                target_pair_actions
                    .entry(kp_local_signature(&poset, &target))
                    .or_default()
                    .insert(kp_pair_action(&target, &raw));
            }
        }
        let source_p_conflicts = source_p_actions
            .values()
            .filter(|actions| actions.len() > 1)
            .count();
        let source_pair_conflicts = source_pair_actions
            .values()
            .filter(|actions| actions.len() > 1)
            .count();
        let target_pair_conflicts = target_pair_actions
            .values()
            .filter(|actions| actions.len() > 1)
            .count();
        let relation_p_conflicts = relation_p_actions
            .values()
            .filter(|actions| actions.len() > 1)
            .count();
        let ordered_p_conflicts = ordered_p_actions
            .values()
            .filter(|actions| actions.len() > 1)
            .count();
        let recorded_pair_conflicts = recorded_pair_actions
            .values()
            .filter(|actions| actions.len() > 1)
            .count();
        let relation_recorded_pair_conflicts = relation_recorded_pair_actions
            .values()
            .filter(|actions| actions.len() > 1)
            .count();
        let trace_pair_conflicts = trace_pair_actions
            .values()
            .filter(|actions| actions.len() > 1)
            .count();
        let boundary_pair_conflicts = boundary_pair_actions
            .values()
            .filter(|actions| actions.len() > 1)
            .count();
        let target_signature_conflicts = target_signature_data
            .values()
            .filter(|(actions, _, _)| actions.len() > 1)
            .count();
        let false_target_signatures = target_signature_data
            .values()
            .filter(|(actions, _, ordinary)| !actions.is_empty() && *ordinary > 0)
            .count();
        let false_target_occurrences: usize = target_signature_data
            .values()
            .filter(|(actions, _, _)| !actions.is_empty())
            .map(|(_, _, ordinary)| ordinary)
            .sum();
        let mut actions_by_target_shape: BTreeMap<(Vec<usize>, Vec<usize>), Vec<KpPairAction>> =
            BTreeMap::new();
        for action in pair_actions.keys() {
            actions_by_target_shape
                .entry((
                    action.p.target_column_shape.clone(),
                    action.q.target_column_shape.clone(),
                ))
                .or_default()
                .push(action.clone());
        }
        let mut replay_recognized_targets = 0;
        let mut replay_missing_targets = 0;
        let mut replay_false_targets = 0;
        let mut replay_ambiguous_targets = 0;
        for poset in natural_unit_interval_orders(n) {
            for key in kp_expected_targets(&poset) {
                let target = kp_insertion_from_key(&key);
                let expected = target_signature_data[&kp_target_signature(&poset, &target)]
                    .0
                    .iter()
                    .next()
                    .cloned();
                let shapes = (
                    target.p_columns.iter().map(Vec::len).collect(),
                    target.q_columns.iter().map(Vec::len).collect(),
                );
                let mut recognized = Vec::new();
                for action in actions_by_target_shape.get(&shapes).into_iter().flatten() {
                    let raw = kp_apply_pair_action(&target, &kp_reverse_pair_action(action));
                    if kp_is_p_tableau(&poset, &raw.p_columns) {
                        continue;
                    }
                    let Some(signature) = kp_boundary_signature_checked(&poset, &raw) else {
                        continue;
                    };
                    if !boundary_pair_actions
                        .get(&signature)
                        .is_some_and(|actions| actions.contains(action))
                    {
                        continue;
                    }
                    if kp_apply_pair_action(&raw, action) != target {
                        continue;
                    }
                    let Some(word) = kp_inverse_checked(&poset, &raw, false) else {
                        continue;
                    };
                    if kp_insert(&poset, &word, false).0 == raw {
                        recognized.push(action.clone());
                    }
                }
                replay_ambiguous_targets += usize::from(recognized.len() > 1);
                match (expected, recognized.as_slice()) {
                    (None, []) => {}
                    (None, _) => replay_false_targets += 1,
                    (Some(_), []) => replay_missing_targets += 1,
                    (Some(expected), [actual]) if *actual == kp_reverse_pair_action(&expected) => {
                        replay_recognized_targets += 1;
                    }
                    (Some(_), _) => replay_false_targets += 1,
                }
            }
        }
        let p_to_q_conflicts = p_to_q_actions
            .values()
            .filter(|actions| actions.len() > 1)
            .count();
        println!(
            "KP corrected n={n}: defects={defects}, same Q={same_recording}, shape changes={shape_changes}, malformed sources={malformed_sources}, P-actions={}, pair-actions={}, max fiber={max_defect_fiber}, ambiguous fibers={ambiguous_defect_fibers}, max exact-Q group={max_exact_q_group}, ambiguous exact-Q groups={ambiguous_exact_q_groups}, movement groups={minimum_movement_groups}, tied movement groups={ambiguous_minimum_movement_groups}, max movement optima={max_minimum_movement_optima}, tied movement profiles={ambiguous_movement_profile_groups}, max profile optima={max_movement_profile_optima}, max height group={max_exact_height_group}, ambiguous height groups={ambiguous_exact_height_groups}, tied height movement={ambiguous_height_movement_groups}, tied height profiles={ambiguous_height_profile_groups}, max height profile optima={max_height_profile_optima}, max residual={max_residual_fiber}, ambiguous residuals={ambiguous_residual_fibers}",
            p_actions.len(),
            pair_actions.len()
        );
        println!(
            "  structural signatures: relation-only={}, conflicts={relation_p_conflicts}; with natural order={}, conflicts={ordered_p_conflicts}; with recording={}, pair-conflicts={relation_recorded_pair_conflicts}; natural+recording={}, pair-conflicts={recorded_pair_conflicts}; with trace kinds={}, pair-conflicts={trace_pair_conflicts}; P-to-Q action conflicts={p_to_q_conflicts}",
            relation_p_actions.len(),
            ordered_p_actions.len(),
            relation_recorded_pair_actions.len(),
            recorded_pair_actions.len(),
            trace_pair_actions.len(),
        );
        println!(
            "  boundary signatures: {}, pair-conflicts={boundary_pair_conflicts}",
            boundary_pair_actions.len(),
        );
        println!(
            "  uniform shape-boundary rule: cases={shape_boundary_cases}, failures={shape_boundary_failures}",
        );
        println!(
            "  recording shape-repair candidates: cases={recording_shape_cases}, failures={recording_shape_failures}, unique={recording_shape_unique}, max-candidates={recording_shape_max_candidates}",
        );
        println!(
            "  uniform transposition rule: cases={transposition_cases}, ties={transposition_ties}, failures={transposition_failures}",
        );
        println!(
            "  local P-Knuth certificates: by-minimal-margin={local_p_knuth_certificates:?}, max-distances={local_p_knuth_max_distances:?}, max-interval={local_p_knuth_max_interval}",
        );
        if n == 7 {
            println!(
                "  uniform candidate graph: edges={uniform_graph_edges}, targets={uniform_graph_targets}, stage-pairs={uniform_graph_stage_pairs:?}, stage-components={uniform_graph_stage_components:?}, total-cost-ties={uniform_graph_total_ties}, profile-ties={uniform_graph_profile_ties}, max-component={uniform_graph_max_source_component}+{uniform_graph_max_target_component}",
            );
        }
        println!(
            "  inverse target signatures: {}, action-conflicts={target_signature_conflicts}, false-recognition signatures={false_target_signatures}, false-recognition targets={false_target_occurrences}",
            target_signature_data
                .values()
                .filter(|(actions, _, _)| !actions.is_empty())
                .count(),
        );
        println!(
            "  inverse replay: recognized={replay_recognized_targets}, missing={replay_missing_targets}, false={replay_false_targets}, ambiguous={replay_ambiguous_targets}",
        );
        let mut p_multiplicities: Vec<usize> = p_actions.into_values().collect();
        p_multiplicities.sort_unstable_by(|left, right| right.cmp(left));
        println!("  P-action multiplicities: {p_multiplicities:?}");
        println!(
            "  local signatures: source P-signatures={}, source P-conflicts={source_p_conflicts}, source pair-signatures={}, source pair-conflicts={source_pair_conflicts}, targets={}, target pair-conflicts={target_pair_conflicts}",
            source_p_actions.len(),
            source_pair_actions.len(),
            target_pair_actions.len(),
        );
        if let Some((code, fiber)) = first_ambiguous {
            println!(
                "  first ambiguous fiber: P={code:?}, Des={}, sources={:?}, targets={:?}",
                fiber.recording_descent_mask, fiber.sources, fiber.targets
            );
        }
        if let Some((code, fiber)) = first_ambiguous_residual {
            println!(
                "  first ambiguous residual: P={code:?}, Des={}, sources={:?}, targets={:?}",
                fiber.recording_descent_mask, fiber.sources, fiber.targets
            );
        }
        if let Some((code, fiber)) = first_ambiguous_exact_q {
            println!(
                "  first ambiguous exact-Q group: P={code:?}, Des={}, sources={:?}, targets={:?}",
                fiber.recording_descent_mask, fiber.sources, fiber.targets
            );
        }
        if let Some((code, fiber)) = first_ambiguous_minimum_movement {
            let costs: Vec<Vec<[usize; 4]>> = fiber
                .sources
                .iter()
                .map(|source| {
                    fiber
                        .targets
                        .iter()
                        .map(|target| kp_pair_action_cost(&source.1, target))
                        .collect()
                })
                .collect();
            println!(
                "  first tied minimum-movement group: P={code:?}, Des={}, sources={:?}, targets={:?}, costs={costs:?}",
                fiber.recording_descent_mask, fiber.sources, fiber.targets,
            );
        }
        if let Some((code, fiber)) = first_ambiguous_movement_profile {
            println!(
                "  first tied movement-profile group: P={code:?}, Des={}, sources={:?}, targets={:?}",
                fiber.recording_descent_mask, fiber.sources, fiber.targets
            );
        }
        if let Some((code, fiber)) = first_ambiguous_height_profile {
            println!(
                "  first tied height-profile group: P={code:?}, Des={}, sources={:?}, targets={:?}",
                fiber.recording_descent_mask, fiber.sources, fiber.targets
            );
        }
        return;
    }
    if args.get(1).map(String::as_str) == Some("--kp-raw") {
        assert_eq!(args.len(), 3, "usage: --kp-raw rank");
        let n = args[2].parse::<usize>().expect("rank must be numeric");
        assert!(n <= 7, "the raw census is bounded to rank at most seven");
        let census = verify_kp_raw_n(n);
        println!(
            "KP raw n={n}: posets={}, ineligible={}, defective={}, words={}, bad P={}, bad Q={}, nonpartition P={}, nonpartition Q={}, collisions={}, bad shapes={:?}",
            census.posets,
            census.ineligible_posets,
            census.defective_posets,
            census.words,
            census.invalid_p,
            census.invalid_q,
            census.nonpartition_p,
            census.nonpartition_q,
            census.collisions,
            census.shape_compositions
        );
        if let Some(witness) = census.first_defect {
            println!(
                "  first defect: P={:?}, word={:?}, output={:?}",
                witness.code, witness.word, witness.insertion
            );
        }
        return;
    }
    if args.get(1).map(String::as_str) == Some("--kp-local") {
        assert_eq!(args.len(), 2, "usage: --kp-local");
        for n in 1..=6 {
            let census = verify_kp_insertion_n(n);
            println!(
                "KP n={n}: posets={}, ineligible={}, defective={}, words={}, raw bad P={}, raw bad Q={}, rank5 repairs={}, corrected bad P={}, collisions={}, missing={}, checksum={}",
                census.posets,
                census.ineligible_posets,
                census.defective_posets,
                census.words,
                census.raw_invalid_p,
                census.raw_invalid_q,
                census.repaired_words,
                census.corrected_invalid_p,
                census.corrected_collisions,
                census.corrected_missing_targets,
                census.trace_checksum
            );
            if let Some(witness) = census.first_defect {
                println!(
                    "  first defect: P={:?}, word={:?}, output={:?}",
                    witness.code, witness.word, witness.insertion
                );
            }
        }

        let mut defect_count = 0;
        let mut p_actions = BTreeSet::new();
        let mut pair_actions = BTreeSet::new();
        let mut source_signatures = BTreeSet::new();
        let mut target_signatures = BTreeSet::new();
        for poset in natural_unit_interval_orders(6) {
            let catalog = kp_correction_catalog(&poset);
            assert_eq!(catalog.forward.len(), 720);
            assert_eq!(catalog.reverse.len(), 720);
            for (_, raw, target) in catalog.defects {
                defect_count += 1;
                p_actions.insert(kp_cell_action(&raw, &target));
                let action = kp_pair_action(&raw, &target);
                assert_eq!(kp_apply_pair_action(&raw, &action), target);
                pair_actions.insert(action);
                source_signatures.insert(kp_local_signature(&poset, &raw));
                target_signatures.insert(kp_local_signature(&poset, &target));
            }
        }
        println!(
            "KP n=6 corrections: defects={defect_count}, P-actions={}, pair-actions={}, source signatures={}, target signatures={}",
            p_actions.len(),
            pair_actions.len(),
            source_signatures.len(),
            target_signatures.len()
        );
        let rank_five_chromatic_catalogs: usize = natural_unit_interval_orders(5)
            .into_iter()
            .map(|poset| {
                let catalog = kp_direct_standard_catalog(&poset);
                assert_eq!(catalog.forward.len(), 120);
                catalog.reverse.len()
            })
            .sum();
        println!(
            "KP n=5 chromatic standard catalogs: {rank_five_chromatic_catalogs} standard pairs"
        );
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
        let p_knuth = verify_p_knuth_components_n(n);
        let direct = verify_direct_map_n(n);
        let (inverse_kostka_states, max_local_events) = verify_inverse_kostka_n(n);
        let (lm_inverse_kostka_states, lm_differing_endpoints, lm_max_local_events) =
            verify_loehr_mendes_inverse_kostka_n(n);
        let inverse_kostka_defects = inverse_kostka_crystal_defects_n(n);
        let summary = verify_n(n);
        let lm_comparison = verify_loehr_mendes_coloring_map_n(n);
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
        println!(
            "  Loehr--Mendes: IK endpoints={} ({} differ from ACM), full-alphabet colorings={}, differing images={}, f differences={}/{} (definedness {}, value {}), S differences={}/{}, max local events={}, max full trace events={}, checksum={}",
            lm_inverse_kostka_states,
            lm_differing_endpoints,
            lm_comparison.colorings,
            lm_comparison.differing_images,
            lm_comparison.differing_lowering,
            lm_comparison.lowering_tests,
            lm_comparison.lowering_definedness_differences,
            lm_comparison.lowering_value_differences,
            lm_comparison.differing_reflections,
            lm_comparison.reflection_tests,
            lm_max_local_events,
            lm_comparison.max_trace_events,
            lm_comparison.trace_checksum
        );
        println!(
            "  P-Knuth direct oracle: posets={}, components={}, anchors={}, excess={}, multi-anchor={}, multi-shape={}, full-alphabet maps={}, targets={}, lowering edges={}, images differing from signed={}",
            p_knuth.posets,
            p_knuth.components,
            p_knuth.anchors,
            p_knuth.anchor_excess,
            p_knuth.multi_anchor_components,
            p_knuth.multi_shape_components,
            direct.colorings,
            direct.targets,
            direct.lowering_edges,
            direct.differing_from_signed
        );
        assert_eq!(direct.posets, p_knuth.posets);
        if let Some(witness) = &p_knuth.first_multi_anchor {
            println!(
                "    first multi-anchor component: P={:?}, size={}, inv={}, shapes={:?}, first={:?}",
                witness.code,
                witness.size,
                witness.inversion,
                witness.anchor_shapes,
                witness.first_word
            );
        }
        if let Some(witness) = &p_knuth.forbidden_component {
            println!(
                "    KP forbidden-word component: P={:?}, size={}, inv={}, shapes={:?}, first={:?}",
                witness.code,
                witness.size,
                witness.inversion,
                witness.anchor_shapes,
                witness.first_word
            );
        }
        if let Some(witness) = &lm_comparison.first_image_difference {
            println!(
                "    first image difference: P={:?}, source={:?}, ACM={:?}, LM={:?}",
                witness.code, witness.source, witness.acm, witness.loehr_mendes
            );
        }
        if let Some(witness) = &lm_comparison.first_lowering_difference {
            println!(
                "    first f difference: P={:?}, root={}, source={:?}, ACM={:?}, LM={:?}",
                witness.code,
                witness.color + 1,
                witness.source,
                witness.acm,
                witness.loehr_mendes
            );
        }
        if let Some(witness) = &lm_comparison.first_reflection_difference {
            println!(
                "    first S difference: P={:?}, root={}, source={:?}, ACM={:?}, LM={:?}",
                witness.code,
                witness.color + 1,
                witness.source,
                witness.acm,
                witness.loehr_mendes
            );
        }
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
    fn loehr_mendes_published_regressions() {
        let lambda = vec![4, 2];
        let tableau = vec![0, 0, 0, 1, 1, 2];
        let composition = vec![1, 3, 2];
        assert_eq!(
            loehr_mendes_normalization_swaps(&composition),
            vec![0, 1, 0, 1]
        );
        let composition_tableau = loehr_mendes_to_composition(&tableau, &lambda, &composition);
        assert_eq!(composition_tableau, vec![0, 1, 1, 1, 2, 2]);
        assert_eq!(
            loehr_mendes_to_partition(&composition_tableau, &lambda, &composition),
            tableau
        );
        // The older stable bubble word has the same target content but a
        // different tableau, so this test distinguishes the exact LM map.
        assert_eq!(
            denormalize_ssyt_content(&tableau, &lambda, &composition),
            vec![0, 1, 1, 2, 1, 2]
        );

        let rank_two = Triple {
            lambda: vec![2],
            pi: vec![0, 1],
            q: vec![0, 1],
        };
        let rank_two_partner = Triple {
            lambda: vec![1, 1],
            pi: vec![1, 0],
            q: vec![0, 1],
        };
        assert_eq!(
            inverse_kostka_loehr_mendes_local(&rank_two, &[2], &[1, 1])
                .unwrap()
                .0,
            rank_two_partner
        );
        assert_eq!(
            inverse_kostka_loehr_mendes_local(&rank_two_partner, &[2], &[1, 1])
                .unwrap()
                .0,
            rank_two
        );

        let example_54 = Triple {
            lambda: vec![2, 2],
            pi: vec![0, 1, 2, 3],
            q: vec![0, 0, 1, 2],
        };
        let example_54_partner = Triple {
            lambda: vec![2, 1, 1],
            pi: vec![0, 2, 1, 3],
            q: vec![0, 0, 1, 2],
        };
        let (actual, events) =
            inverse_kostka_loehr_mendes_local(&example_54, &[2, 2], &[2, 1, 1]).unwrap();
        assert_eq!(actual, example_54_partner);
        assert_eq!(events.len(), 3);
        assert_eq!(
            inverse_kostka_loehr_mendes_local(&example_54_partner, &[2, 2], &[2, 1, 1])
                .unwrap()
                .0,
            example_54
        );

        // The published example separating Loehr--Mendes from
        // Allen--Celano--Mason.
        let published = Triple {
            lambda: vec![3, 2, 1],
            pi: vec![1, 2, 0, 3, 4, 5],
            q: vec![0, 0, 0, 1, 1, 2],
        };
        let published_lm_partner = Triple {
            lambda: vec![4, 2],
            pi: vec![1, 0, 2, 3, 4, 5],
            q: vec![0, 0, 0, 1, 1, 2],
        };
        let (actual, events) =
            inverse_kostka_loehr_mendes_local(&published, &[5, 1], &[3, 2, 1]).unwrap();
        assert_eq!(actual, published_lm_partner);
        assert_eq!(events.len(), 19);
        assert_eq!(
            inverse_kostka_loehr_mendes_local(&published_lm_partner, &[5, 1], &[3, 2, 1])
                .unwrap()
                .0,
            published
        );
        assert_eq!(
            inverse_kostka_local(&published, &[5, 1], &[3, 2, 1])
                .unwrap()
                .0
                .q,
            vec![0, 0, 0, 2, 1, 1]
        );
    }

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
    fn forbidden_p_knuth_component_has_published_schur_inventory() {
        let poset = Poset {
            h: vec![1, 3, 3, 4, 4],
        };
        let component = p_knuth_components(&poset)
            .into_iter()
            .find(|component| component.contains(&vec![2, 3, 4, 1, 0]))
            .unwrap();
        assert_eq!(component.len(), 19);
        let component_set: BTreeSet<Vec<usize>> = component.into_iter().collect();
        let mut anchors = BTreeMap::new();
        for lambda in partitions(5) {
            let p_shape = conjugate_partition(&lambda);
            for tableau in p_tableaux(&poset, &lambda) {
                let word = p_tableau_column_word(&tableau);
                if component_set.contains(&word) {
                    assert!(anchors.insert(word, p_shape.clone()).is_none());
                }
            }
        }
        assert_eq!(
            anchors,
            BTreeMap::from([
                (vec![2, 0, 4, 3, 1], vec![4, 1]),
                (vec![4, 0, 3, 1, 2], vec![4, 1]),
                (vec![4, 1, 3, 0, 2], vec![3, 2]),
                (vec![4, 2, 0, 3, 1], vec![3, 1, 1]),
            ])
        );
    }

    #[test]
    fn exhaustive_through_four() {
        for n in 1..=4 {
            verify_p_knuth_components_n(n);
            verify_direct_map_n(n);
            verify_inverse_kostka_n(n);
            verify_loehr_mendes_inverse_kostka_n(n);
            verify_loehr_mendes_coloring_map_n(n);
            verify_n(n);
            verify_one_empty_color_n(n);
        }
    }

    #[test]
    fn semistandard_lusztig_involution_is_the_crystal_involution() {
        let lambda = vec![2, 1];
        let standard = vec![0, 1, 2];
        assert_eq!(
            tableau_lusztig_involution(&lambda, &standard, 3),
            vec![0, 2, 1]
        );

        for n in 1..=5 {
            for content in compositions(n) {
                let alphabet = content.len();
                for lambda in partitions(n) {
                    for q in ssyts(&lambda, &content) {
                        let eta = tableau_lusztig_involution(&lambda, &q, alphabet);
                        assert_eq!(shape(&eta, alphabet), {
                            let mut reversed = content.clone();
                            reversed.reverse();
                            reversed
                        });
                        assert_eq!(tableau_lusztig_involution(&lambda, &eta, alphabet), q);
                        assert_eq!(
                            standardize_semistandard_tableau(&lambda, &eta),
                            evacuate_standard_tableau(
                                &lambda,
                                &standardize_semistandard_tableau(&lambda, &q),
                            )
                        );
                        let target = Target {
                            lambda: lambda.clone(),
                            t: Vec::new(),
                            q: q.clone(),
                        };
                        let eta_target = Target {
                            lambda: lambda.clone(),
                            t: Vec::new(),
                            q: eta,
                        };
                        for color in 0..alphabet.saturating_sub(1) {
                            let eta_after_f =
                                crystal_on_target(&target, color, false).map(|moved| {
                                    tableau_lusztig_involution(&lambda, &moved.q, alphabet)
                                });
                            let e_after_eta =
                                crystal_on_target(&eta_target, alphabet - 2 - color, true)
                                    .map(|moved| moved.q);
                            assert_eq!(eta_after_f, e_after_eta);
                        }
                    }
                }
            }
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
    fn kim_pylyavskyy_rank_five_climber_repair_is_recording_aware() {
        let poset = Poset {
            h: vec![1, 3, 3, 4, 4],
        };
        let (first_raw, first_trace) = kp_insert(&poset, &[2, 3, 4, 1, 0], false);
        assert_eq!(
            kp_tableau_key(&first_raw),
            (vec![3, 2], vec![2, 0, 1, 4, 3], vec![0, 1, 4, 2, 3])
        );
        assert!(!first_trace.repaired_rank_five_climber);
        assert_eq!(
            first_trace
                .passes
                .iter()
                .flat_map(|pass| &pass.events)
                .filter(|event| matches!(event.kind, KpColumnEventKind::LadderMove))
                .count(),
            2
        );

        let (second_raw, _) = kp_insert(&poset, &[2, 4, 1, 3, 0], false);
        assert_eq!(
            kp_tableau_key(&second_raw),
            (vec![3, 2], vec![2, 0, 1, 4, 3], vec![0, 2, 4, 1, 3])
        );
        assert!(!kp_is_p_tableau(&poset, &first_raw.p_columns));
        assert!(!kp_is_p_tableau(&poset, &second_raw.p_columns));
        assert!(kp_is_standard_tableau(&first_raw.q_columns));
        assert!(kp_is_standard_tableau(&second_raw.q_columns));

        let (first_repaired, first_repair_trace) = kp_insert(&poset, &[2, 3, 4, 1, 0], true);
        let (second_repaired, second_repair_trace) = kp_insert(&poset, &[2, 4, 1, 3, 0], true);
        assert_eq!(
            kp_tableau_key(&first_repaired),
            (vec![3, 2], vec![1, 0, 2, 4, 3], vec![0, 1, 4, 2, 3])
        );
        assert_eq!(
            kp_tableau_key(&second_repaired),
            (vec![3, 2], vec![1, 0, 2, 4, 3], vec![0, 2, 4, 1, 3])
        );
        assert!(first_repair_trace.repaired_rank_five_climber);
        assert!(second_repair_trace.repaired_rank_five_climber);
        assert_eq!(first_repair_trace.raw_p_columns, first_raw.p_columns);
        assert_eq!(second_repair_trace.raw_p_columns, second_raw.p_columns);
        assert!(kp_is_p_tableau(&poset, &first_repaired.p_columns));
        assert!(kp_is_p_tableau(&poset, &second_repaired.p_columns));
        assert_eq!(
            kp_inverse(&poset, &first_repaired, true),
            vec![2, 3, 4, 1, 0]
        );
        assert_eq!(
            kp_inverse(&poset, &second_repaired, true),
            vec![2, 4, 1, 3, 0]
        );

        for word in [[3, 4, 1, 0, 2], [4, 1, 3, 0, 2], [4, 1, 3, 2, 0]] {
            let (existing, trace) = kp_insert(&poset, &word, true);
            assert_eq!(
                kp_columns_to_rows(&existing.p_columns),
                vec![vec![1, 0, 2], vec![4, 3]]
            );
            assert!(!trace.repaired_rank_five_climber);
            assert_eq!(kp_inverse(&poset, &existing, true), word);
        }
    }

    #[test]
    fn kim_pylyavskyy_repaired_bijection_through_five() {
        for n in 1..=5 {
            let census = verify_kp_insertion_n(n);
            assert_eq!(census.words, census.posets * (1..=n).product::<usize>());
            assert_eq!(census.raw_invalid_q, 0);
            assert_eq!(census.corrected_invalid_p, 0);
            assert_eq!(census.corrected_collisions, 0);
            assert_eq!(census.corrected_missing_targets, 0);
            if n < 5 {
                assert_eq!(census.raw_invalid_p, 0);
                assert_eq!(census.repaired_words, 0);
            } else {
                assert_eq!(census.ineligible_posets, 1);
                assert_eq!(census.defective_posets, 0);
                assert_eq!(census.raw_invalid_p, 2);
                assert_eq!(census.repaired_words, 2);
            }
        }
    }

    #[test]
    fn garsia_milne_hybrid_extends_raw_kp() {
        let poset = Poset {
            h: vec![1, 3, 3, 4, 4],
        };
        let hybrid = kp_garsia_milne_catalog(&poset);
        assert_eq!(hybrid.raw_good_words, 118);
        assert_eq!(hybrid.corrected_words, 2);
        assert!(hybrid.max_alternating_steps > 0);
        for word in permutations(5) {
            let image = &hybrid.standard.forward[&word];
            assert_eq!(hybrid.standard.reverse[image], word);
            let (raw, _) = kp_insert(&poset, &word, false);
            if kp_is_p_tableau(&poset, &raw.p_columns) && kp_is_standard_tableau(&raw.q_columns) {
                assert_eq!(*image, kp_insertion_direct_image(&poset, &word, &raw));
            }
        }
        let alphabet = 3;
        for coloring in proper_colorings(&poset, alphabet) {
            let content = shape(&coloring, alphabet);
            let target = direct_forward_with_catalog(&poset, &coloring, alphabet, &hybrid.standard);
            assert_eq!(
                direct_reverse_with_catalog(&poset, &target, &content, &hybrid.standard),
                coloring
            );
            assert_eq!(asc(&poset, &coloring), inv_g(&poset, &target.t));
            for color in 0..alphabet - 1 {
                if let Some(lowered) = direct_coloring_crystal_operator(
                    &poset,
                    &coloring,
                    alphabet,
                    color,
                    false,
                    &hybrid.standard,
                ) {
                    assert_eq!(
                        direct_coloring_crystal_operator(
                            &poset,
                            &lowered,
                            alphabet,
                            color,
                            true,
                            &hybrid.standard,
                        ),
                        Some(coloring.clone())
                    );
                }
            }
        }
    }

    #[test]
    fn kim_pylyavskyy_chromatic_bijection_through_five() {
        for n in 1..=5 {
            for poset in natural_unit_interval_orders(n) {
                let catalog = kp_direct_standard_catalog(&poset);
                let mut images_by_weight: BTreeMap<Vec<usize>, BTreeSet<Target>> = BTreeMap::new();
                for source in proper_colorings(&poset, n) {
                    let content = shape(&source, n);
                    let target = direct_forward_with_catalog(&poset, &source, n, &catalog);
                    assert_eq!(
                        direct_reverse_with_catalog(&poset, &target, &content, &catalog),
                        source
                    );
                    assert_eq!(asc(&poset, &source), inv_g(&poset, &target.t));
                    assert_eq!(shape(&target.q, n), content);
                    for color in 0..n.saturating_sub(1) {
                        if let Some(lowered) = direct_coloring_crystal_operator(
                            &poset, &source, n, color, false, &catalog,
                        ) {
                            assert_eq!(
                                direct_coloring_crystal_operator(
                                    &poset, &lowered, n, color, true, &catalog,
                                ),
                                Some(source.clone())
                            );
                            assert_eq!(asc(&poset, &lowered), asc(&poset, &source));
                        }
                    }
                    assert!(images_by_weight.entry(content).or_default().insert(target));
                }
                for (content, images) in images_by_weight {
                    assert_eq!(images, target_fiber(&poset, &content).into_iter().collect());
                }
            }
        }
    }

    #[test]
    fn kim_pylyavskyy_rank_six_defect_census() {
        let census = verify_kp_insertion_n(6);
        assert_eq!(census.posets, 132);
        assert_eq!(census.ineligible_posets, 12);
        assert_eq!(census.defective_posets, 12);
        assert_eq!(census.words, 95_040);
        assert_eq!(census.raw_invalid_p, 112);
        assert_eq!(census.raw_invalid_q, 0);
        assert_eq!(census.repaired_words, 0);
        assert_eq!(census.corrected_invalid_p, 112);
        assert_eq!(census.corrected_collisions, 0);
        assert_eq!(census.corrected_missing_targets, 112);
        let witness = census.first_defect.unwrap();
        assert_eq!(witness.code.len(), 6);
        assert_eq!(witness.word.len(), 6);
        assert_eq!(
            kp_tableau_key(&witness.insertion).0.iter().sum::<usize>(),
            6
        );
    }

    #[test]
    fn kim_pylyavskyy_rank_eight_recording_defects() {
        let descent_poset = Poset {
            h: vec![0, 1, 3, 5, 5, 6, 6, 7],
        };
        let descent_word = vec![7, 1, 0, 4, 5, 6, 3, 2];
        let (descent_raw, _) = kp_insert(&descent_poset, &descent_word, false);
        let required_descent = reverse_descent_positions(
            p_descent_mask(&descent_poset, &descent_word),
            descent_word.len(),
        );
        assert_ne!(
            kp_recording_descent_mask(&descent_raw.q_columns),
            required_descent
        );

        let recording_poset = Poset {
            h: vec![1, 3, 4, 5, 6, 7, 7, 7],
        };
        let recording_word = vec![6, 2, 0, 4, 5, 7, 3, 1];
        let (recording_raw, _) = kp_insert(&recording_poset, &recording_word, false);
        assert!(kp_is_p_tableau(&recording_poset, &recording_raw.p_columns));
        assert!(!kp_is_standard_tableau(&recording_raw.q_columns));
        assert!(kp_first_invalid_boundary(&recording_poset, &recording_raw.p_columns).is_none());
        assert!(kp_first_invalid_recording_boundary(&recording_raw.q_columns).is_some());
    }

    #[test]
    fn kim_pylyavskyy_rank_six_forced_corrections() {
        let mut defect_count = 0;
        let mut same_recording = 0;
        let mut shape_changes = 0;
        let mut actions = BTreeMap::new();
        let mut forward_signatures = BTreeMap::new();
        let mut inverse_signatures = BTreeMap::new();
        let mut forward_conflicts = 0;
        let mut inverse_conflicts = 0;
        for poset in natural_unit_interval_orders(6) {
            let catalog = kp_correction_catalog(&poset);
            for (word, raw, target) in &catalog.defects {
                defect_count += 1;
                same_recording += usize::from(raw.q_columns == target.q_columns);
                shape_changes += usize::from(
                    raw.p_columns.iter().map(Vec::len).collect::<Vec<_>>()
                        != target.p_columns.iter().map(Vec::len).collect::<Vec<_>>(),
                );
                let action = kp_cell_action(raw, target);
                *actions.entry(action.clone()).or_insert(0) += 1;
                let pair_action = kp_pair_action(raw, target);
                if let Some(old) =
                    forward_signatures.insert(kp_local_signature(&poset, raw), pair_action.clone())
                {
                    forward_conflicts += usize::from(old != pair_action);
                }
                let inverse_action = kp_pair_action(target, raw);
                if let Some(old) = inverse_signatures
                    .insert(kp_local_signature(&poset, target), inverse_action.clone())
                {
                    inverse_conflicts += usize::from(old != inverse_action);
                }
                assert_eq!(kp_apply_pair_action(raw, &pair_action), *target);
                assert_eq!(kp_apply_pair_action(target, &inverse_action), *raw);
                assert_eq!(catalog.forward[word], *target);
                assert_eq!(catalog.reverse[target], *word);
            }
        }
        assert_eq!(defect_count, 112);
        assert_eq!(same_recording, 106);
        assert_eq!(shape_changes, 6);
        let mut action_multiplicities: Vec<usize> = actions.into_values().collect();
        action_multiplicities.sort_unstable();
        assert_eq!(action_multiplicities, [2, 3, 4, 4, 6, 6, 7, 12, 14, 54]);
        assert_eq!(forward_signatures.len(), 77);
        assert_eq!(inverse_signatures.len(), 77);
        assert_eq!(forward_conflicts, 0);
        assert_eq!(inverse_conflicts, 0);

        let mut decoded_repairs = 0;
        let mut false_inverse_guards = 0;
        for poset in natural_unit_interval_orders(6) {
            let catalog = kp_correction_catalog(&poset);
            let defect_targets: BTreeSet<KpInsertion> = catalog
                .defects
                .iter()
                .map(|(_, _, target)| target.clone())
                .collect();
            for key in kp_expected_targets(&poset) {
                let target = kp_insertion_from_key(&key);
                let Some(inverse_action) =
                    inverse_signatures.get(&kp_local_signature(&poset, &target))
                else {
                    continue;
                };
                let raw = kp_apply_pair_action(&target, inverse_action);
                if kp_is_p_tableau(&poset, &raw.p_columns) {
                    continue;
                }
                let Some(forward_action) =
                    forward_signatures.get(&kp_local_signature(&poset, &raw))
                else {
                    continue;
                };
                if kp_apply_pair_action(&raw, forward_action) != target {
                    continue;
                }
                let Some(word) = kp_inverse_checked(&poset, &raw, false) else {
                    continue;
                };
                if kp_insert(&poset, &word, false).0 != raw {
                    continue;
                }
                if defect_targets.contains(&target) {
                    decoded_repairs += 1;
                } else {
                    false_inverse_guards += 1;
                }
            }
        }
        assert_eq!(decoded_repairs, 112);
        assert_eq!(false_inverse_guards, 0);

        let poset = Poset {
            h: vec![2, 2, 4, 4, 5, 5],
        };
        let catalog = kp_correction_catalog(&poset);
        let word = vec![3, 5, 2, 0, 4, 1];
        let (_, raw, target) = catalog
            .defects
            .iter()
            .find(|(source, _, _)| *source == word)
            .unwrap();
        assert_eq!(raw.p_columns, [vec![5, 3], vec![4, 0], vec![2], vec![1]]);
        assert_eq!(raw.q_columns, [vec![1, 0], vec![4, 2], vec![3], vec![5]]);
        assert_eq!(target.p_columns, [vec![5, 2], vec![4, 0], vec![3, 1]]);
        assert_eq!(target.q_columns, [vec![1, 0], vec![4, 2], vec![5, 3]]);
    }

    #[test]
    fn kim_pylyavskyy_published_rank_seven_nonshape_output() {
        let poset = Poset {
            h: vec![1, 3, 4, 5, 5, 6, 6],
        };
        let word = vec![2, 0, 4, 5, 6, 3, 1];
        let (raw, _) = kp_insert(&poset, &word, false);
        assert_eq!(raw.p_columns, [vec![2, 0], vec![6, 4, 1], vec![5], vec![3]]);
        assert_eq!(raw.q_columns, [vec![2, 0], vec![6, 3, 1], vec![4], vec![5]]);
        assert_eq!(
            raw.p_columns.iter().map(Vec::len).collect::<Vec<_>>(),
            [2, 3, 1, 1]
        );
        assert_eq!(kp_inverse(&poset, &raw, false), word);
        let repaired = kp_shape_boundary_repair(&poset, &raw).unwrap();
        assert_eq!(
            repaired.p_columns,
            [vec![2, 0], vec![6, 3], vec![5, 1], vec![4]]
        );
        assert_eq!(
            repaired.q_columns,
            [vec![2, 0], vec![3, 1], vec![6, 4], vec![5]]
        );
        assert!(kp_is_p_tableau(&poset, &repaired.p_columns));
        assert!(kp_is_standard_tableau(&repaired.q_columns));
        assert_eq!(kp_correction_catalog(&poset).forward[&word], repaired);
        let recording_candidates = kp_recording_shape_repair_candidates(&raw);
        assert_eq!(recording_candidates.len(), 2);
        assert!(recording_candidates.contains(&repaired.q_columns));
    }

    #[test]
    fn kim_pylyavskyy_rank_seven_minimum_movement_matching() {
        let crossed_poset = Poset {
            h: vec![1, 2, 4, 4, 5, 6, 6],
        };
        let crossed = kp_correction_catalog(&crossed_poset);
        let uniform = kp_uniform_graph_catalog(&crossed_poset);
        let crossed_targets: BTreeMap<_, _> = crossed
            .defects
            .iter()
            .map(|(word, _, target)| (word.clone(), target.clone()))
            .collect();
        let uniform_targets: BTreeMap<_, _> = uniform
            .pairs
            .iter()
            .map(|((word, _), target)| (word.clone(), target.clone()))
            .collect();
        assert_eq!(uniform_targets, crossed_targets);
        assert_eq!(uniform.profile_ties, 0);
        for word in permutations(7) {
            let target = kp_uniform_forward(&crossed_poset, &word, &uniform);
            assert_eq!(target, crossed.forward[&word]);
            assert_eq!(kp_uniform_reverse(&crossed_poset, &target, &uniform), word);
        }
        let first_word = vec![0, 3, 4, 6, 5, 2, 1];
        let second_word = vec![3, 2, 5, 4, 6, 1, 0];
        assert_eq!(
            crossed.forward[&first_word].p_columns,
            [vec![6, 0], vec![5, 2], vec![1], vec![4], vec![3]]
        );
        assert_eq!(
            crossed.forward[&second_word].p_columns,
            [vec![5, 1], vec![4, 0], vec![2], vec![3], vec![6]]
        );
        let (_, second_raw, second_target) = crossed
            .defects
            .iter()
            .find(|(word, _, _)| *word == second_word)
            .unwrap();
        let repairs = kp_boundary_transposition_repairs(&crossed_poset, second_raw);
        assert_eq!(repairs.len(), 1);
        assert_eq!(repairs[0], *second_target);
        assert_eq!(crossed.ambiguous_movement_profile_groups, 0);

        let left_shape_poset = Poset {
            h: vec![1, 3, 4, 5, 5, 6, 6],
        };
        let left_shape_word = vec![6, 4, 2, 3, 5, 1, 0];
        let left_shape_catalog = kp_correction_catalog(&left_shape_poset);
        let (_, left_shape_raw, left_shape_target) = left_shape_catalog
            .defects
            .iter()
            .find(|(word, _, _)| *word == left_shape_word)
            .unwrap();
        let recording_candidates = kp_recording_shape_repair_candidates(left_shape_raw);
        assert_eq!(recording_candidates.len(), 2);
        assert!(recording_candidates.contains(&left_shape_target.q_columns));
        assert_eq!(
            left_shape_target
                .q_columns
                .iter()
                .map(Vec::len)
                .collect::<Vec<_>>(),
            [3, 2, 1, 1]
        );

        let tied_total_poset = Poset {
            h: vec![1, 3, 4, 5, 6, 6, 6],
        };
        let tied_total = kp_correction_catalog(&tied_total_poset);
        let first_word = vec![4, 3, 2, 6, 5, 1, 0];
        let second_word = vec![5, 3, 2, 6, 4, 1, 0];
        assert_eq!(
            tied_total.forward[&first_word].p_columns,
            [vec![5, 1], vec![6, 0], vec![4], vec![3], vec![2]]
        );
        assert_eq!(
            tied_total.forward[&second_word].p_columns,
            [vec![6, 1], vec![4, 0], vec![5], vec![3], vec![2]]
        );
        assert!(tied_total.ambiguous_minimum_movement_groups > 0);
        assert_eq!(tied_total.ambiguous_movement_profile_groups, 0);
        assert_eq!(tied_total.ambiguous_height_profile_groups, 0);

        let recording_poset = Poset {
            h: vec![2, 2, 4, 4, 5, 5, 6],
        };
        let recording_catalog = kp_correction_catalog(&recording_poset);
        let first_word = vec![3, 2, 6, 5, 4, 0, 1];
        let second_word = vec![3, 4, 6, 2, 5, 0, 1];
        let (_, first_raw, first_target) = recording_catalog
            .defects
            .iter()
            .find(|(word, _, _)| *word == first_word)
            .unwrap();
        let (_, second_raw, second_target) = recording_catalog
            .defects
            .iter()
            .find(|(word, _, _)| *word == second_word)
            .unwrap();
        assert_eq!(first_raw.p_columns, second_raw.p_columns);
        assert_eq!(
            kp_recording_descent_mask(&first_raw.q_columns),
            kp_recording_descent_mask(&second_raw.q_columns)
        );
        assert_ne!(
            kp_pair_action(first_raw, first_target),
            kp_pair_action(second_raw, second_target)
        );
        assert_ne!(
            kp_boundary_signature(&recording_poset, first_raw),
            kp_boundary_signature(&recording_poset, second_raw)
        );
        let first_action = kp_pair_action(first_raw, first_target);
        assert_eq!(
            kp_apply_pair_action(first_target, &kp_reverse_pair_action(&first_action)),
            *first_raw
        );
    }

    #[test]
    fn kim_pylyavskyy_rank_seven_coloring_crystal_sample() {
        let poset = Poset {
            h: vec![1, 2, 4, 4, 5, 6, 6],
        };
        let alphabet = 3;
        let catalog = kp_direct_standard_catalog(&poset);
        let colorings = proper_colorings(&poset, alphabet);
        assert!(!colorings.is_empty());
        let mut lowering_edges = 0;
        for source in colorings {
            let content = shape(&source, alphabet);
            let target = direct_forward_with_catalog(&poset, &source, alphabet, &catalog);
            assert_eq!(
                direct_reverse_with_catalog(&poset, &target, &content, &catalog),
                source
            );
            assert_eq!(asc(&poset, &source), inv_g(&poset, &target.t));
            assert_eq!(shape(&target.q, alphabet), content);
            for color in 0..alphabet - 1 {
                if let Some(lowered) = direct_coloring_crystal_operator(
                    &poset, &source, alphabet, color, false, &catalog,
                ) {
                    lowering_edges += 1;
                    assert_eq!(
                        direct_coloring_crystal_operator(
                            &poset, &lowered, alphabet, color, true, &catalog,
                        ),
                        Some(source.clone())
                    );
                }
            }
        }
        assert!(lowering_edges > 0);
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
