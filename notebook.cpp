// tplt
void dfs (int u) {
    low[u] = num[u] = ++timeDfs;
    st.push(u);

    for (auto v : g[u]) {
        if (deleted[v]) continue;
        if (!num[v]) {
            dfs (v);
            low[u] = min (low[u], low[v]);
        } else low[u] = min (low[u], num[v]);
    }
    if (low[u] == num[u]) {
        mark[u] = ++cnt;
        int v;
        do {
            v = st.top();
            st.pop();
            mark[v] = mark[u];
            deleted[v] = 1;
        } while (u != v);
    }
}

// khop va cau
void dfs (int u, int pre) {
    int child = 0;
    low[u] = num[u] = ++timeDfs;

    for (auto v : g[u]) {
        if (v == pre) continue;
        if (!num[v]) {
            dfs (v, u);
            low[u] = min (low[u], low[v]);
            if (low[v] == num[v]) bridge ++;
            child ++;
            
            if (u == pre) {
                if (child > 1) mark[u] = 1;
            } else if (low[v] >= num[u]) mark[u] = 1;
        } else low[u] = min (low[u], num[v]);
    }
}

// binary lifting
void dfs(int u, int pre) {
    up[u][0].first = pre;
    for(auto x : g[u]) {
        int v = x.first, cost = x.second;
        if(v == pre) continue;
        h[v] = h[u] + 1;
        up[v][0].second = cost;
        dfs(v, u);
    }
}

void buildLca() {
    FOR(i, 1, 15) {
        FOR(u, 1, n) {
            up[u][i].first = up[up[u][i - 1].first][i - 1].first;
            up[u][i].second = up[up[u][i - 1].first][i - 1].second + up[u][i - 1].second;
        }
    }
}

int getbit(int val, int pos) {
    return ((val >> pos) & 1);
}

int solve(int u, int v) {
    if(h[u] < h[v]) swap(u, v);

    int res = 0;
    int diff = h[u] - h[v];
    FOR(i, 0, 15) {
        if(getbit(diff, i)) {
            res += up[u][i].second;
            u = up[u][i].first;
        }
    }
    
    if(u == v) return res;
    FOD(i, 15, 0) {
        if(up[u][i].first != up[v][i].first) {
            res += up[u][i].second + up[v][i].second; 
            u = up[u][i].first;
            v = up[v][i].first;
        }
    }

    return res + up[u][0].second + up[v][0].second;
}

// hld

void hld(int u) {

    // N???u chu???i hi???n t???i ch??a c?? ?????nh ?????u (?????nh g???n g???c nh???t) th?? ?????t u l??m ?????nh ?????u c???a n??.
	if (chainHead[nChain] == 0) chainHead[nChain] = u;

    // G??n chu???i hi???n t???i cho u
	chainInd[u] = nChain;

    // Gi???i th??ch b??n d?????i
	posInBase[u] = ++nBase;

    // Bi???n l??u ?????nh con ?????c bi???t c???a u
	int mxVtx = -1;

    // T??m ?????nh con ?????c bi???t trong s??? nh???ng ?????nh con c???a u
	for (int i = 0; i < adj[u].size(); i++) {
		int v = adj[u][i];
		if (v != parent[u]) {
			if (mxVtx == -1 || nChild[v] > nChild[mxVtx]) {
				mxVtx = v;
			}
		}	
	}

    // N???u t??m ra ?????nh con ?????c bi???t (u kh??ng ph???i l?? ?????nh l??) th?? di chuy???n ?????n ?????nh ????
	if (mxVtx > -1)
		hld(mxVtx);

    // Sau khi ??i h???t m???t chu???i th?? t??ng nChain l??n v?? b???t ?????u m???t chu???i m???i
	for (int i = 0; i < adj[u].size(); i++) {
		int v = adj[u][i];
		if (v != parent[u] && v != mxVtx) {
			nChain++;
			hld(v);
		}
	}
}

void update(int u, int a) {
    // uchain chu???i hi???n t???i c???a u 
    // achain chu???i c???a a
     int uchain = chainInd[u], achain = chainInd[a];

     while (1) {
        // N???u u v?? a c??ng n???m tr??n m???t chu???i th?? update ??o???n t??? u ?????n a v?? k???t th??c.
          if (uchain == achain) {
               updateIntervalTree(..., posInBase[a], posInBase[u], ...);
               break;
          }
        // N???u u v?? a kh??ng n???m tr??n c??ng m???t chu???i th?? update ??o???n t??? u ?????n ?????nh ?????u c???a chu???i hi???n t???i.
          updateIntervalTree(..., posInBase[chainHead[uchain]], posInBase[u], ...);

        // Nh???y l??n ?????nh cha c???a ?????nh ?????u hi???n t???i.
          u = parent[chainHead[uchain]];
          uchain = chainInd[u];
     }
}

// Suffix Array

namespace SuffixArray
{
    const int MAXN = 1e5 + 5;
    string S;
    int N, gap;
    int sa[MAXN], pos[MAXN], tmp[MAXN], lcp[MAXN];

    bool sufCmp(int i, int j)
    {
        if (pos[i] != pos[j])
            return pos[i] < pos[j];
        i += gap;
        j += gap;
        return (i < N && j < N) ? pos[i] < pos[j] : i > j;
    }

    void buildSA()
    {
        N = S.size();
        for (int i = 0; i < N; i ++) sa[i] = i, pos[i] = S[i];
        for (gap = 1;; gap *= 2)
        {
            sort(sa, sa + N, sufCmp);
            for (int i = 0; i < N - 1; i ++) tmp[i + 1] = tmp[i] + sufCmp(sa[i], sa[i + 1]);
            for (int i = 0; i < N; i ++) pos[sa[i]] = tmp[i];
            if (tmp[N - 1] == N - 1) break;
        }
    }

    void buildLCP()
    {
        for (int i = 0, k = 0; i < N; ++i) if (pos[i] != N - 1)
        {
            for (int j = sa[pos[i] + 1]; S[i + k] == S[j + k];)
            ++k;
            lcp[pos[i]] = k;
            if (k)--k;
        }
    }
}

int cmp (int l1, int r1, int l2, int r2) {
    int le = 1, ri = min (r1 - l1, r2 - l2) + 1;

    // Matching ans character
    int ans = 0;
    while (le <= ri) {
        int m = (le + ri) / 2;

        if (get (l1, l1 + m - 1) == get (l2, l2 + m - 1)) {
            ans = max (ans, m);
            le = m + 1;
        } else ri = m - 1;
    }    

    if (l1 + ans == r1 + 1) {
        if (r1 - l1 == r2 - l2) return 0;
        else return -1;
    }

    if (l2 + ans == r2 + 1) {
        if (r1 - l1 == r2 - l2) return 0;
        else return 1;
    }

    if (s[l1 + ans] < s[l2 + ans]) return -1;
    else return 1;
}

int findLe (int length) {
    int l = 0, r = n - 1, ans = n;
    while (l <= r) {
        int m = (l + r) / 2;

        int tmp = cmp (sa[m] + 1, sa[m] + length, 1, length);
        if (tmp <= 0) {
            if (tmp == 0) {
                ans = min (ans, m);
                r = m - 1;
            }
            else l = m + 1;
        } else r = m - 1; 
    }

    return ans;
}

int fineRi (int length) {
    int l = 0, r = n - 1, ans = -10;
    while (l <= r) {
        int m = (l + r) / 2;

        int tmp = cmp (sa[m] + 1, sa[m] + length, 1, length);
        if (tmp >= 0) {
            if (tmp == 0) {
                ans = max (ans, m);
                l = m + 1;
            }
            else r = m - 1;
        } else l = m + 1;
    }

    return ans;
}