use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

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
    },
}

#[derive(Clone, Debug)]
struct Catalog {
    positive: Vec<Triple>,
    negative: Vec<Triple>,
    exceptional: bool,
}

impl Catalog {
    fn partner(&self, triple: &Triple) -> Option<Triple> {
        if permutation_sign(&triple.pi) > 0 {
            let index = self
                .positive
                .binary_search(triple)
                .expect("positive triple missing from catalog");
            if self.exceptional && index == 0 {
                None
            } else {
                let negative_index = if self.exceptional { index - 1 } else { index };
                Some(self.negative[negative_index].clone())
            }
        } else {
            let index = self
                .negative
                .binary_search(triple)
                .expect("negative triple missing from catalog");
            let positive_index = if self.exceptional { index + 1 } else { index };
            Some(self.positive[positive_index].clone())
        }
    }

    fn canonical_fixed(&self) -> Triple {
        assert!(self.exceptional);
        self.positive[0].clone()
    }
}

#[derive(Default)]
struct Catalogs {
    map: HashMap<(usize, Vec<usize>, Vec<usize>), Catalog>,
}

impl Catalogs {
    fn get(&mut self, n: usize, nu: &[usize], mu: &[usize]) -> &Catalog {
        let key = (n, nu.to_vec(), mu.to_vec());
        self.map
            .entry(key)
            .or_insert_with(|| build_catalog(n, nu, mu))
    }
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
    Catalog {
        positive,
        negative,
        exceptional,
    }
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

fn forward(
    poset: &Poset,
    coloring: &[usize],
    catalogs: &mut Catalogs,
) -> (Target, Vec<TraceEvent>) {
    let k = 1 + *coloring.iter().max().unwrap();
    let mu = shape(coloring, k);
    let oriented = orient_asc_to_des(poset, coloring, k);
    assert_eq!(shape(&oriented, k), mu);
    assert_eq!(des(poset, &oriented), asc(poset, coloring));
    let mut padded_mu = mu.clone();
    padded_mu.resize(poset.n(), 0);
    let (normalized, _) = normalize(poset, &oriented, &padded_mu);
    let mu_plus = decreasing_rearrangement(&mu);
    let triple = catalogs.get(poset.n(), &mu_plus, &mu).canonical_fixed();
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
        let catalog = catalogs.get(poset.n(), &nu, &mu);
        state.triple = catalog
            .partner(&state.triple)
            .expect("negative state cannot be fixed by inverse-Kostka involution");
        assert_eq!(catalog.partner(&state.triple), Some(old.clone()));
        trace.push(TraceEvent::InverseKostka {
            nu,
            from: old,
            to: state.triple.clone(),
        });
    }
    panic!("Garsia--Milne forward path exceeded safety bound");
}

fn reverse(poset: &Poset, target: &Target, mu: &[usize], catalogs: &mut Catalogs) -> Vec<usize> {
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
        let Some(partner) = catalogs.get(n, &nu, mu).partner(&state.triple) else {
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

fn trace_checksum(trace: &[TraceEvent]) -> usize {
    trace
        .iter()
        .map(|event| match event {
            TraceEvent::Sw(event) => event.row + event.col + event.normalize_swaps.len(),
            TraceEvent::InverseKostka { nu, from, to } => {
                nu.iter().sum::<usize>() + from.lambda.len() + to.lambda.len()
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
        let mut catalogs = Catalogs::default();
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
                let (target, trace) = forward(&poset, source, &mut catalogs);
                assert_eq!(asc(&poset, source), inv_g(&poset, &target.t));
                assert_eq!(reverse(&poset, &target, &mu, &mut catalogs), *source);
                assert!(images.insert(target));
                summary.max_trace_events = summary.max_trace_events.max(trace.len());
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

fn main() {
    verify_lgv_obstruction();
    verify_all_tail_q_obstruction();
    println!("LGV obstruction: n=2, mu=(1,1), nu=(2), lambda changes (2) <-> (1,1)");
    println!("all-tail q obstruction: n=4, m=(1,3,3,4), G={{2,3}}, q changes 0 -> 1");
    let mut total = Summary::default();
    for n in 1..=5 {
        let summary = verify_n(n);
        println!(
            "n={n}: posets={} (KP {}), packed proper colorings={} (KP {}), targets={}, max_trace_events={}, checksum={}",
            summary.posets,
            summary.kp_posets,
            summary.colorings,
            summary.kp_colorings,
            summary.targets,
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
            verify_n(n);
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
}
