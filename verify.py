"""Build actual proofs, then audit every project theorem's transitive axioms."""
from pathlib import Path
import json
import re
import shutil
import subprocess
import sys

sys.stdout.reconfigure(encoding='utf-8')

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'verification'
OUT.mkdir(exist_ok=True)
lake = shutil.which('lake')
if not lake:
    raise SystemExit('Lake is unavailable')

def run(args, filename):
    result = subprocess.run([lake, *args], cwd=ROOT, capture_output=True,
                            encoding='utf-8', errors='replace')
    output = result.stdout + result.stderr
    (OUT / filename).write_text(output, encoding='utf-8')
    if result.returncode:
        print(output)
        raise SystemExit(result.returncode)
    return output

run(['build', 'GMZP0', 'GMZP0.Audit'], 'build.log')
output = run(['env', 'lean', 'GMZP0/Audit.lean'], 'axioms.log')

def without_comments(source):
    """Remove line and nested block comments before the complementary lexical guard."""
    out, i, depth = [], 0, 0
    while i < len(source):
        if source.startswith('/-', i):
            depth += 1
            out.append(' ')
            i += 2
        elif depth and source.startswith('-/', i):
            depth -= 1
            out.append(' ')
            i += 2
        elif depth:
            out.append('\n' if source[i] == '\n' else ' ')
            i += 1
        elif source.startswith('--', i):
            end = source.find('\n', i)
            i = len(source) if end < 0 else end
        else:
            out.append(source[i])
            i += 1
    if depth:
        raise SystemExit('Unclosed Lean block comment')
    return ''.join(out)

theorems = set()
for path in (ROOT / 'GMZP0').glob('*.lean'):
    source = without_comments(path.read_text(encoding='utf-8'))
    for name in re.findall(r'\btheorem\s+(\w+)', source):
        theorems.add('GMZP0.' + name)
    # This lexical guard complements, and does not replace, the kernel axiom report.
    if re.search(r'\b(?:sorry|admit|axiom)\b', source):
        raise SystemExit(f'Unproved placeholder or axiom declaration in {path.name}')
reports = re.findall(r"'(GMZP0\.\w+)' depends on axioms: \[([^\]]*)\]", output)
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
audit = {}
for name, values in reports:
    axioms = {v.strip() for v in values.split(',') if v.strip()}
    if not axioms <= allowed:
        raise SystemExit(f'Unexpected axiom dependency: {name}: {axioms - allowed}')
    audit[name] = sorted(axioms)
if set(audit) != theorems:
    raise SystemExit(f'Incomplete audit: missing={theorems - set(audit)}; extra={set(audit) - theorems}')
result = dict(build='passed', checked_theorems=len(audit), transitive_axioms=audit,
              main_P0='NOT_proved', weighted_capture='NOT_proved',
              conditional_P0_reduction='checked: WeightedCapture -> P0',
              conditional_terminal_capture='checked: explicit model approximation and finite minor-arc operator estimates imply original-weight finite capture',
              original_first_adjoint='checked: exact finite adjoint, endpoint Gram expansion, I/N same-horizontal block, original-weight energy lower bound and first grouped TT* inequality',
              second_adjoint_statistic='checked with explicit horizontal window X; normalized second diagonal <= mu(D)/N; complete original-label reindexing proves equality to the finite lag-indexed signed statistic at total scale N^(-6)',
              safe_window='checked: M=ceil(64/kappa), c=kappa/(4M), exact interval partition, original mass and supported original targets',
              positive_safe_statistic='checked: constants and scale threshold precede all original data; exact finite and lag statistics are equal and >= 2*zeta > 0, with original responses retained',
              lag_reindexing='checked: single block, full double-label sum, (r1,r2) to (k,r) and t=r+k-h finite-sum bijections; k=0 contribution explicit, nonnegative and <= mu(D)/N; original targets and weights preserved',
              rerooted_average='checked: exact g(k)e(P(k)) factorization, B normalized by N, S_lag+D_lag equals N^(-5) outer weighted sum, |g| and |B| <= 1, uniform positive finite modulus average',
              cyclic_average='checked: original supported field values and B survive cyclic embedding; complete horizontal reindexing has 2N shifts; exact finite modulus average = (2q/N^2) * cyclic modulus average; constants precede N, q and all original data; cyclic mean >= zeta/128, with weights in [0,1] on a 2qN^3-point sample space',
              prime_modulus='checked from Mathlib Bertrand: for every N>0 there is a prime 64N^2<q<128N^2',
              smoothing='checked: interval translation error for all signed shifts and empty intervals; four independent shifts on exactly (2*ell+1)^4 points; N-normalized error <= 8*ell/N <= a/8; the smoothed original weighted mean is >=7*a/8 with all constants preceding N, q and original data',
              cubic_faces='checked: explicit four unit circle-phase factors, each independent of its own coordinate; exact factorization of the actual cyclic smoothed sequence',
              box_cauchy_schwarz='checked for every dimension: coordinate doubling preserves unit face factors and independence; nonnegative recursively defined box moments and exact root-power identity; actual four-shift sequence is bounded by its box norm',
              positive_box_average='checked: weights removed only from a nonnegative box norm; full lag extension costs (2N+1)/N<=3; finite moment Jensen gives average box moment >=(a/4)^16 on 2qN^3(2N+1) outer samples; constants precede N, q and original data, original mass and complete response retained',
              cube_expansion='checked in every dimension: exact complex equality of recursive moment and full Boolean-vertex product with multiplicities and parity conjugation; four-dimensional shift pairs have (2*ell+1)^8 points',
              cube_rerooting='checked: full cyclic average reindexed by Y=y+2hk with explicit inverse; sixteen weights and alternating alignments factored; t-cubic coefficient is minus the signed original frequency sum and independent of k',
              weighted_time_average='checked: full t average separated by an exact finite bijection; all sixteen weights remain in an average >=(a/4)^16 with constants before N, q and original data; each nonzero-weight cube vertex is an actual retained original base point with the original complete response',
              linear_weyl='checked: inverse chord and geometric sums give ||a|| <= 1/(2*rho*N) for every affine phase and every integer interval with original N normalization',
              weyl_differencing='checked: exact whole pair-sum identity, explicit zero shift <=1, at least N*rho^2/4 nonzero signed shifts above rho^2/8 when N*rho^2>=2; exact N=1 obstruction to dropping this threshold',
              polynomial_differences='checked: exact circle-valued quadratic/cubic derivatives on actual overlap intervals; quadratic large shifts satisfy ||2*h*a2|| <= 4/(rho^2*N), without changing N normalization',
              affine_recurrence_seed='checked: explicit pigeonhole cardinality condition gives two nearby actual returns and a nonzero bounded multiple',
              affine_recurrence='checked: bounded actual rounding fibers amplify epsilon to E*epsilon/N when epsilon*N<=C; positive denominator bound, error factor and threshold precede N, a, b, epsilon and the retained set',
              quadratic_weyl='checked at every N>0: uniform bounded positive denominator and N^(-2) leading-coefficient error; actual shorter intervals retain their original N normalization',
              cubic_weyl='checked at every N>0: exact differencing, actual quadratic denominator fiber and affine recurrence give uniform bounded positive denominator and N^(-3) leading-coefficient error',
              common_denominator='checked: factorial of the uniform denominator bound yields one positive denominator fixed before N and all polynomial/original data',
              weighted_cube_capture='checked: actual original cubic time sum has the checked leading coefficient; successful N^(-3) cube coefficients retain original weighted mean >=(a/4)^16/2, all constants before N,q and original data, with original safe mass and complete responses preserved',
              lag_and_sign_reduction='checked: unused k average removed exactly; simultaneous h/shift reflection fixes every actual vertex and preserves all weights; positive-h mean equals the original signed mean',
              cube_collisions='checked: short shift interval embeds, 2h is nonzero for positive labels at the chosen scale, coordinate resampling gives pair probability <=1/(2*ell+1), all 120 unordered pairs give total <=120/(2*ell+1); zero modular step obstruction proved',
              distinct_original_cube_capture='checked: one scale threshold fixed before q and all original data ensures weighted distinct-vertex cube mass >=(a/4)^16/4 for prime q in the original range, while original safe mass and complete responses remain',
              real_lift_rounding='checked: one [0,1) representative, actual nearest integer, eight positive and eight negative signs, S=l*M+r with |l|<=8 and |r|<=9, and one allowed local correction makes the real cube sum exactly zero',
              global_assignment='checked: restriction of the full point-choice product to any injective vertex family is uniform; local success has probability >=57^(-16); finite weighted expectation produces one choice shared by all cubes without independence between cubes',
              simultaneous_real_lift='checked: M_lift=floor(N^3/E)>=9, all point values lie in M_lift^(-1)Z, |F|<=3, zero original weight gives F=0, supported circle error to d*theta is <=19*E/N^3, and original weighted real-zero cube mass is >=(a/4)^16/(4*57^16); all constants precede N,q and original data, original complete responses retained',
              exact_frequency_mesh='checked: all dimensions d<=7, grid differences k/M with |k|<=384M<1024M, complete j/1024 character orthogonality detects exact real zero; integer-frequency and missing-size-bound obstructions are proved',
              local_four_average='checked: generic finite multiset local moments are nonnegative, local norms have the exact 2^s power and are <=1 for bounded fields; the actual weighted mesh average equals the original real-zero four-cube mass with every multiplicity retained',
              original_local_fibres='checked: uniform original-data theorem gives local fourth-norm sixteenth moment >=beta=(a/4)^16/(4*57^16) and proportion >=beta/2 of actual (x,j) fibres with mean_h local norm >=beta/2; one fixed F, prior constants, original safe mass and full responses preserved',
              finite_fourier='checked: probability-normalized coefficients, unnormalized character synthesis, finite inversion and Parseval; difference correlation has coefficients |nu_hat|^2 with sum exactly E nu^2',
              parameter_difference_density='checked: actual parameter multiplicities give density |G|*count/|A| relative to uniform measure; exact weighted pushforward, independent pair differences, full product law, and density L2 <= |G|*K/|A| from representation multiplicity K',
              local_fourier_expansion='checked: local paired-shift moment equals the global additive cube mean weighted by the actual difference density; explicit nonnegative Fourier expansion retains all multiplicities and yields a bound conditional on every character-twisted global cube average',
              local_global_comparison='checked for every s>=2: all character-twisted global cube averages are bounded by the untwisted moment; actual multiset local moment <= C^s times global moment whenever the original uniform density energy <=C; no unproved twist or mixed-CS premise remains; exact norm and positive lower-moment consequences checked; family concatenation remains unproved',
              global_frequency_average='checked for every 1<=s<=7: the complete finite mesh mean of the global s-moment equals the weighted real-zero cube mass of the same F; actual cyclic seventh-moment identity preserves all original weights, without asserting an unproved positive lower bound',
              twisted_cube='checked: exact derivative recurrence, two-dimensional Fourier energy base, translation square-sum estimate and induction; exact one-dimensional nontrivial-character obstruction also checked',
              pair_geometry='PARTIAL: checked elementary paired-shift prerequisites, including a<=256 from the actual local-four bound, uniform shrink threshold, integer range and modular no-wrap; gcd representation multiplicity and exceptional-pair count remain unproved',
              bounded_box_faces='checked in every dimension: the face-factor Cauchy-Schwarz estimate allows norm <=1, with independence and all finite means retained; this is not being asserted as a full mixed Gowers inequality',
              density_normalization_obstruction='checked: on ZMod 2 a constant function disproves use of raw probability masses in place of density relative to the uniform mean',
              cube_extraction='PARTIAL overall: original weighted circle cubes, one simultaneous real lift, local fourth moments, positive good-fibre density, full local-to-global comparison and exact global seventh-moment frequency averaging are checked; uniform family concatenation, actual pair geometry and deeper value extraction remain open',
              proof_scope='Phase algebra, exact original input geometry and two weighted finite adjoints with separate diagonals, response comparison, full-label metric and scaling, complete circle roots, universal major-arc grid, weighted energy and mass, and conditional reductions to capture and P0')
(OUT / 'result.json').write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
print(f'Build passed; {len(audit)} theorem declarations audited; only standard foundations occur.')
print('P0 and WeightedCapture remain unproved propositions.')
