"""spec §5 の性質 P1〜P6 と決定 D4・D5・D13 を、有理数で厳密に検査する。"""

from fractions import Fraction

import numpy as np
import pytest
from hypothesis import given, settings
from hypothesis import strategies as st

from picsy.core import (
    InvalidOperation,
    cancel,
    remaining,
    NotUnique,
    State,
    contributions,
    freeze,
    join,
    recover,
    remove,
    transact,
    uniform_J,
    vcb,
)

F = Fraction


@st.composite
def eval_matrix(draw, min_n=3, max_n=6, positive_budget=False):
    """非負・行和1の有理数行列。positive_budget なら全員 E_ii > 0。"""
    n = draw(st.integers(min_n, max_n))
    rows = []
    for i in range(n):
        w = draw(st.lists(st.integers(0, 6), min_size=n, max_size=n))
        if positive_budget and w[i] == 0:
            w[i] = 1
        if sum(w) == 0:
            w[i] = 1
        t = sum(w)
        rows.append([F(x, t) for x in w])
    return np.array(rows, dtype=object)


fractions01 = st.fractions(min_value=0, max_value=1, max_denominator=20)


def is_stochastic(M):
    return all(x >= 0 for x in M.flat) and all(sum(r) == 1 for r in M)


@given(eval_matrix())
def test_P1_vcb_is_stochastic_with_zero_diagonal(E):
    Ep = vcb(E)
    assert is_stochastic(Ep)
    assert all(Ep[i, i] == 0 for i in range(len(E)))


@given(eval_matrix(), st.data())
def test_P3_transaction_preserves_invariants(E, data):
    n = len(E)
    b = data.draw(st.integers(0, n - 1))
    s = data.draw(st.integers(0, n - 1).filter(lambda x: x != b))
    if E[b, b] == 0:
        with pytest.raises(InvalidOperation):
            transact(State(E), b, s, F(1, 100))
        return
    r = data.draw(st.fractions(min_value=0, max_value=1, max_denominator=20).filter(lambda x: x > 0))
    E2 = transact(State(E), b, s, r * E[b, b]).E
    assert is_stochastic(E2)


@given(eval_matrix(), st.data())
def test_D5_overdraft_is_rejected(E, data):
    n = len(E)
    with pytest.raises(InvalidOperation):
        transact(State(E), 0, 1, E[0, 0] + F(1, 1000))
    with pytest.raises(InvalidOperation):
        transact(State(E), 0, 0, F(0))


@given(eval_matrix(), fractions01.filter(lambda g: 0 < g < 1))
def test_P4_recovery(E, g):
    n = len(E)
    E2 = recover(State(E), g).E
    assert is_stochastic(E2)
    assert all(E2[i, i] >= g for i in range(n))
    expected = (1 - g) * vcb(E) + g * uniform_J(n, exact=True)
    assert (vcb(E2) == expected).all()


@settings(max_examples=60)
@given(eval_matrix(positive_budget=True))
def test_P5_join_keeps_contributions_and_budgets(E):
    n = len(E)
    c = contributions(E)
    assert sum(c) == n
    E2 = join(State(E), c).E
    assert is_stochastic(E2)
    assert all(E2[i, i] == E[i, i] for i in range(n)) and E2[n, n] == 0
    c2 = contributions(E2)
    assert list(c2) == list(c) + [1]


@given(eval_matrix(min_n=4), st.data())
def test_P6_removal_preserves_invariants(E, data):
    d = data.draw(st.integers(0, len(E) - 1))
    st2 = remove(freeze(State(E), d), d)
    assert st2.N == len(E) - 1
    assert is_stochastic(st2.E)


@settings(max_examples=80)
@given(eval_matrix(positive_budget=True), st.data())
def test_D13_cancel_restores_counterfactual(E, data):
    """取引のあとに取引・自然回収を混ぜた列が続いても、残量を差し引けば
    「その取引が無かった列」の結果に正確に一致する（Lean の cancel_exact・cancel_stochastic）。"""
    n = len(E)
    b = data.draw(st.integers(0, n - 1))
    s = data.draw(st.sampled_from([j for j in range(n) if j != b]))
    alpha = E[b, b] * data.draw(st.fractions(min_value=F(1, 10), max_value=1, max_denominator=10))
    actual = transact(State(E), b, s, alpha)
    counter = State(E)
    gammas = []
    for _ in range(data.draw(st.integers(0, 6))):
        if data.draw(st.booleans()):
            g = data.draw(st.sampled_from([F(1, 20), F(1, 10), F(1, 2)]))
            actual, counter = recover(actual, g), recover(counter, g)
            gammas.append(g)
        else:
            b2 = data.draw(st.integers(0, n - 1))
            s2 = data.draw(st.sampled_from([j for j in range(n) if j != b2]))
            budget = actual.E[b2, b2]  # 実際の列で前提を満たす量にする
            if budget == 0:
                continue
            a2 = budget * data.draw(st.sampled_from([F(1, 4), F(1, 2), F(1)]))
            actual, counter = transact(actual, b2, s2, a2), transact(counter, b2, s2, a2)
    undone = cancel(actual, b, s, remaining(alpha, gammas))
    assert (undone.E == counter.E).all()
    assert is_stochastic(undone.E)


def test_frozen_member_cannot_trade():
    E = np.array([[F(int(i == j)) for j in range(4)] for i in range(4)], dtype=object)
    s = freeze(State(E), 2)
    with pytest.raises(InvalidOperation):
        transact(s, 2, 0, F(1, 2))
    with pytest.raises(InvalidOperation):
        transact(s, 0, 2, F(1, 2))


def link_farm():
    """予算を使い切った2組が、それぞれ組の中だけを評価している状態（spec D4 の反例）。"""
    E = np.zeros((6, 6), dtype=object)
    E[:] = F(0)
    for a, b in [(0, 1), (1, 0), (2, 3), (3, 2)]:
        E[a, b] = F(1)
    E[4, 4] = F(1)
    E[5, 5] = F(1)
    return E


def test_D4_strict_raises_on_two_closed_classes():
    with pytest.raises(NotUnique) as ei:
        contributions(link_farm())
    assert sorted(map(sorted, ei.value.classes)) == [[0, 1], [2, 3]]


def test_D4_damped_is_unique():
    c = contributions(link_farm(), eta=F(1, 10))
    assert sum(c) == 6 and all(x > 0 for x in c)


def test_float_and_exact_agree():
    rng = np.random.default_rng(0)
    E = rng.random((7, 7))
    E /= E.sum(1, keepdims=True)
    Ex = np.array([[F(x).limit_denominator(10**6) for x in r] for r in E], dtype=object)
    Ex = np.array([[x / sum(r) for x in r] for r in Ex], dtype=object)
    cf = contributions(Ex.astype(float))
    cx = np.array(contributions(Ex), dtype=float)
    assert np.allclose(cf, cx, atol=1e-9)
    # べき乗法とも一致する
    M = vcb(Ex.astype(float))
    v = np.ones(7)
    for _ in range(2000):
        v = v @ M
    assert np.allclose(v / v.sum() * 7, cf, atol=1e-9)
