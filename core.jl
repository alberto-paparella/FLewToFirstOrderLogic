using SoleLogics
using SoleLogics.ManyValuedLogics
using UUIDs
using SoleLogics: AbstractAlgebra
using SoleLogics.ManyValuedLogics: FiniteIndexFLewAlgebra, FiniteIndexTruth

struct Point
    value::String
end

struct Interval
    x::Point
    y::Point
end

# """
# The natural definition of many-valued Allen's relations. 
# For every X ∈ {A, Ai, L, Li, B, Bi, E, Ei, D, Di, O, Oi} we have RX: I(D)×I(D)→H defined by:

#  - RA([x,y],[z,t]) = =(y,z)
#  - RL([x,y],[z,t]) = <(y,z)
#  - RB([x,y],[z,t]) = =(x,z) ∩ <(t,y)
#  - RE([x,y],[z,t]) = <(x,z) ∩ =(y,t)
#  - RD([x,y],[z,t]) = <(x,z) ∩ <(t,y)
#  - RO([x,y],[z,t]) = <(x,z) ∩ <(z,y) ∩ <(y,t)

# and similarly for the inverse relations:

# - RAi([x,y],[z,t]) = =(t,x)
# - RLi([x,y],[z,t]) = <(t,x)
# - RBi([x,y],[z,t]) = =(z,x) ∩ <(y,t)
# - REi([x,y],[z,t]) = <(z,x) ∩ =(t,y)
# - RDi([x,y],[z,t]) = <(z,x) ∩ <(y,t)
# - ROi([x,y],[z,t]) = <(z,x) ∩ <(x,t) ∩ <(y,t)
# """
# function mveval(
#     r::R,
#     (x,y)::Tuple{Point,Point},
#     (z,t)::Tuple{Point,Point}
# ) where {
#     R<:AbstractRelation
# }
#     if r == SoleLogics.IA_A
#         "(mveq $(y.label) $(z.label))"
#     elseif r == SoleLogics.IA_L
#         "(mvlt $(y.label) $(z.label))"
#     elseif r == SoleLogics.IA_B
#         "(monoid (mveq $(x.label) $(z.label)) (mvlt $(t.label) $(y.label)))"
#     elseif r == SoleLogics.IA_E
#         "(monoid (mvlt $(x.label) $(z.label)) (mveq $(y.label) $(t.label)))"
#     elseif r == SoleLogics.IA_D
#         "(monoid (mvlt $(x.label) $(z.label)) (mvlt $(t.label) $(y.label)))"
#     elseif r == SoleLogics.IA_O
#         "(monoid (monoid (mvlt $(x.label) $(z.label)) (mvlt $(z.label) $(y.label))) (mvlt $(y.label) $(t.label)))"
#     elseif r == SoleLogics.IA_Ai
#         "(mveq $(t.label) $(x.label))"
#     elseif r == SoleLogics.IA_Li
#         "(mvlt $(t.label) $(x.label))"
#     elseif r == SoleLogics.IA_Bi
#         "(monoid (mveq $(z.label) $(x.label)) (mvlt $(y.label) $(t.label)))"
#     elseif r == SoleLogics.IA_Ei
#         "(monoid (mvlt $(z.label) $(x.label)) (mveq $(t.label) $(y.label)))"
#     elseif r == SoleLogics.IA_Di
#         "(monoid (mvlt $(z.label) $(x.label)) (mvlt $(y.label) $(t.label)))"
#     elseif r == SoleLogics.IA_Oi
#         "(monoid (monoid (mvlt $(z.label) $(x.label)) (mvlt $(x.label) $(t.label))) (mvlt $(t.label) $(y.label)))"
#     else
#         error("Relation $r not in HS")
#     end
# end

"""
Translate the α-satisfiability for mvhs into first-order using smt-lib syntax.
"""
function translate(φ::F, α::FiniteIndexTruth, algebra::FiniteIndexFLewAlgebra{N}) where {F<:Formula, N}
    # algebra
    smtfile = "(declare-sort A)\n"
    for i ∈ 1:N
        smtfile *= "(declare-const a$i A)\n"
    end
    smtfile *= "(assert (distinct"
    for i ∈ 1:N
        smtfile *= " a$i"
    end
    smtfile *= "))\n(declare-fun join (A A) A)\n(declare-fun meet (A A) A)\n(declare-fun monoid (A A) A)\n(declare-fun implication (A A) A)\n"
    for i ∈ 1:N
        for j ∈ 1:N
            smtfile *= "(assert (= (join a$i a$j) a$(algebra.join(UInt8(i), UInt8(j)).index)))\n"
            smtfile *= "(assert (= (meet a$i a$j) a$(algebra.meet(UInt8(i), UInt8(j)).index)))\n"
            smtfile *= "(assert (= (monoid a$i a$j) a$(algebra.monoid(UInt8(i), UInt8(j)).index)))\n"
            smtfile *= "(assert (= (implication a$i a$j) a$(algebra.implication(UInt8(i), UInt8(j)).index)))\n"
        end
    end
    smtfile *= "(define-fun precedeq ((x A) (y A)) Bool (= (meet x y) x))\n"
    # order
    smtfile *= "(declare-sort W)\n"
    smtfile *= "(declare-fun mveq (W W) A)\n"
    smtfile *= "(declare-fun mvlt (W W) A)\n"
    smtfile *= "(assert (forall ((x W) (y W)) (= (= (mveq x y) a1) (= x y))))\n"                                                                   # =(x,y) = 1 iff x = y
    smtfile *= "(assert (forall ((x W) (y W)) (= (mveq x y) (mveq y x))))\n"                                                                       # =(x,y) = =(y,x)
    smtfile *= "(assert (forall ((x W)) (= (mvlt x x) a2)))\n"                                                                                      # <(x,x) = 0
    smtfile *= "(assert (forall ((x W) (y W) (z W)) (precedeq (monoid (mvlt x y) (mvlt y z)) (mvlt x z))))\n"                                       # <(x,z) ⪰ <(x,y) ⋅ <(y,z)
    smtfile *= "(assert (forall ((x W) (y W) (z W)) (=> (and (distinct (mvlt x y) a2) (distinct (mvlt y z) a2)) (distinct (mvlt x z) a2))))\n"    # if <(x,y) ≻ 0 and <(y,z) ≻ 0 then <(x,z) ≻ 0
    smtfile *= "(assert (forall ((x W) (y W)) (=> (and (= (mvlt x y) a2) (= (mvlt y x) a2)) (= (mveq x y) a1))))\n"                                # if <(x,y) = 0 and <(y,x) = 0 then =(x,y) = 1
    smtfile *= "(assert (forall ((x W) (y W)) (=> (distinct (mveq x y) a2) (distinct (mvlt x y) a1))))\n"                                          # if =(x,y) ≻ 0 then <(x,y) ≺ 1

    w = Interval(Point("x"),Point("y"))
    atoms = Vector{Atom}()
    translation = translate(φ, w, α, algebra, atoms)
    for p ∈ atoms
        smtfile *= "(declare-fun P (W W A) Bool)\n"
    end
    smtfile *= "(assert (exists ((x W) (y W)) $(translation)))\n"

    smtfile *= "(check-sat)"
    b = IOBuffer()
    uuid = UUIDs.uuid4()
    touch("$(tempdir())/temp$uuid.smt2")
    open("$(tempdir())/temp$uuid.smt2", "w") do file
        write(file, smtfile)
    end
    run(pipeline(`z3 $(tempdir())/temp$uuid.smt2`, stdout = b))
    rm("$(tempdir())/temp$uuid.smt2")
    return take!(b) == UInt8[0x73, 0x61, 0x74, 0x0a]
end

"""
Translate the α-satisfiability for mvhs into first-order using smt-lib syntax.
"""
function translate(φ::F, α::T, algebra::A) where {T<:Truth, F<:Formula, A<:AbstractAlgebra}
    if !isa(α, FiniteIndexTruth) α = convert(FiniteIndexTruth, α) end
    if !isa(algebra, FiniteIndexFLewAlgebra) algebra = convert(FiniteIndexFLewAlgebra, algebra) end
    translate(φ, α, algebra)
end

function translate(p::Atom, w::Interval, _::FiniteIndexTruth, _::FiniteIndexFLewAlgebra{N}, atoms::Vector{Atom}) where {N}
    if p ∉ atoms push!(atoms, p) end
    smtfile = "(or"
    for value in 1:N
        smtfile *= " (P $(w.x.value) $(w.y.value) a$value)"
    end
    smtfile *= ")"
    return smtfile
end

function translate(β::T, w::Interval, α::FiniteIndexTruth, _::FiniteIndexFLewAlgebra, atoms::Vector{Atom}) where {T<:Truth}
    if !isa(β, FiniteIndexTruth) β = convert(FiniteIndexTruth, β) end
    return "(precedeq a$(α.index) a$(β.index))"
end

function translate(φ::SyntaxBranch, )