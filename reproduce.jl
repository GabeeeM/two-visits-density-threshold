# Constructive proof of: Σ 1/d_i ≤ 1  ⇒  2-Visits schedulable.
# Generalized statement T(b): positions c+1..c+2n, sorted g, (i) Σ1/g + c/(2g_1) ≤ 1, (ii) g_k ≥ c+k.
# Returns vectors (x, y) of absolute positions (first, second visit) for tasks in sorted order.

# check (b)
condb(g, c) = (n = length(g); n == 0 || (all(g[k] >= c + k for k in 1:n) &&
               sum(1 // big(x) for x in g) + big(c) // (2 * g[1]) <= 1))

# block for a C-instance (all g ≤ c+n, (ii), (i)); returns slot i and second-slot σ per task (sorted order)
function cblock(g, c)
    n = length(g); K = n - c
    d = count(<(n), g)
    slot = zeros(Int, n); sig = zeros(Int, n)
    cells = Tuple{Int,Int}[]                    # (slot, σ) for non-deficit tasks
    pos = 0
    if d > 0
        @assert c >= 1
        δ = [n - g[j] for j in 1:d]; E = min(d, cld(c, 2))
        for k0 in 1:E:d
            G = k0:min(d, k0 + E - 1); q = δ[k0]
            # merge order: deficit j preceded by B_j = q - δ_j partners
            pp = 1; r = 0
            for (i, j) in enumerate(G)
                B = q - δ[j]
                while pp <= B; r += 1; push!(cells, (pos + pp, pos + r)); pp += 1; end
                r += 1; slot[j] = pos + q + i; sig[j] = pos + r
            end
            while pp <= q; r += 1; push!(cells, (pos + pp, pos + r)); pp += 1; end
            pos += q + length(G)
        end
    end
    for i in pos+1:n; push!(cells, (i, i)); end
    req = [max(s - i, i - K) for (i, s) in cells]
    perm = sortperm(req)
    for (a, t) in zip(perm, d+1:n)               # sorted cells → sorted non-deficit tasks
        slot[t], sig[t] = cells[a]
    end
    slot, sig
end

# main recursive construction; g sorted
function tb(g, c)
    n = length(g)
    n == 0 && return (Int[], Int[])
    n == 1 && return ([c + 1], [c + 2])
    # split?
    for s in 1:n-1
        if all(g[s+k] >= c + 2s + k for k in 1:n-s)
            x1, y1 = tb(g[1:s], c); x2, y2 = tb(g[s+1:n], c + 2s)
            return (vcat(x1, x2), vcat(y1, y2))
        end
    end
    # irreducible: core
    w = maximum(r for r in 2:n if g[r] == c + r)
    D = n - w
    slot, sig = cblock(g[1:w] .- D, c - D)
    x = zeros(Int, n); y = zeros(Int, n)
    for t in 1:w; x[t] = c + slot[t]; y[t] = c + n + sig[t]; end
    for t in w+1:n; x[t] = c + t; y[t] = c + n + t; end
    (x, y)
end

function validate(g, c, x, y)
    n = length(g)
    pos = vcat(x, y)
    sort(pos) == collect(c+1:c+2n) || return false
    all(x[t] < y[t] && x[t] <= g[t] && y[t] - x[t] <= g[t] for t in 1:n)
end

# ---------------- reproduction of all reported numbers ----------------
using Random
# brute-force 2-Visits feasibility (small n) via pair assignment DFS
function feasible_bf(d)
    n=length(d)
    # simpler exhaustive: schedules as permutations of multiset, n ≤ 4
    function dfs(pos, cnt, first)
        pos>2n && return true
        for i in 1:n
            if cnt[i]==0 && pos<=d[i]
                cnt[i]=1; first[i]=pos
                dfs(pos+1,cnt,first) && return true
                cnt[i]=0
            elseif cnt[i]==1 && pos-first[i]<=d[i]
                cnt[i]=2
                dfs(pos+1,cnt,first) && return true
                cnt[i]=1
            end
        end
        false
    end
    dfs(1,zeros(Int,n),zeros(Int,n))
end

function enum_dens1(n, cb)
    d=zeros(Int,n)
    function rec(k,lo,s)
        if k>n; cb(d); return; end
        for v in lo:2n+1
            ns=s+1//v
            ns + (n-k)//(2n+1) > 1 && continue
            d[k]=v; rec(k+1,v,ns)
        end
    end
    rec(1,1,0//1)
end

println("1) exhaustive check of the constructive proof, all sorted deadline vectors with density ≤ 1 (deadlines ≤ 2n+1)")
tot=0
for n in 1:10
    cnt=0; bad=0
    enum_dens1(n, d->begin
        cnt+=1; x,y=tb(copy(d),0); validate(d,0,x,y) || (bad+=1)
    end)
    global tot+=cnt
    println("   n=$n instances=$cnt invalid=$bad")
end
println("   total=$tot")

println("2) random instances with density ≤ 1, n ≤ 60 (1,000,000 seeds)")
let cnt=0, bad=0
    for s in 1:1_000_000
        rng=Xoshiro(s); n=rand(rng,1:60)
        k=rand(rng,1:4); vals=rand(rng,1:3n,k); d=sort([rand(rng,vals) for _ in 1:n])
        sum(1//big(x) for x in d)<=1 || continue
        cnt+=1; x,y=tb(d,0); validate(d,0,x,y) || (bad+=1)
    end
    println("   instances=$cnt invalid=$bad")
end

println("3) the earlier unit-cycle block fails but chunk block works: c=6, g=[20^3,30^21]")
let g=vcat(fill(20,3),fill(30,21)), c=6
    n=length(g); d=3; δ=[n-g[j] for j in 1:d]
    println("   unit-cycle slot condition D_j+δ_j+j ≤ K: ", all(sum(δ[1:j])+δ[j]+j <= n-c for j in 1:d))
    sl,sg=cblock(g,c)
    ok = sort(sl)==1:n && sort(sg)==1:n && all(c+sl[t]<=g[t] && n+sg[t]-sl[t]<=g[t] for t in 1:n)
    println("   chunk block valid: ", ok)
end

println("4) sharpness: k+1 copies of k are unschedulable (brute force, k=1..3); density (k+1)/k")
for k in 1:3
    println("   k=$k density=$(Float64((k+1)/k)) schedulable=", feasible_bf(fill(k,k+1)))
end
