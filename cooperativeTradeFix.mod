reset;
model;

## A-Balanced-Multi-team-Formation-Problem-under-Synergy-Superstar-and-Preference-Considerations ##


######## SETS ####################################################
set T; # all teams
set Arcs within T cross T; # (i,j) in T
set F; # free agents (i_f) 
set F_; # players in free agents C[i_f]
set D; # draftees (id) 
set D_; # players in draftees C[id]
set N; # all nodes (teams + id + i_f) := T union F union D;
set C_; # all players
set C{N}; # players belonging to node N 
set P; # all positions
set Q{P}; # players belonging to position P
set R{T}; # draft positions of team T
# adding superstars
set S_; # superstars
set TS; # teams with superstars
set S{TS}; # superstars belonging to node TS
### adding synergy sets ###
set G_; # archetypes
set G{G_}; # players in archetype G_
set U; # linearizaiton set


######## PARAMETERS ##############################################
param v{C_}; # individual value of player 
param z{F_,T}; # ordinal preference of free agents to teams
param m{C_}; # contract cost of player
param b{T}; # budget of team 
param wL{T,P}; # lower bound of position P requirement for team T
param wU{T,P}; # upper bound of position P requirement for team T
param pMax{T}; # 15 - number of current players on team T
param rv; # individual value fairness tolerance
param rm; # contractual fairness tolerance
param M; # big M
# adding econ value
param vBar{S_}; # economic value of superstars 
### adding synergy ###
param b_synergy{G_,G_}; # synergy for between groups

##### DECISION VARIABLES #######################################s##
var X{i in N diff D, t in T, C[i]: i <> t}, binary; # 1 if player C leaves node N to team T (update indices)
var Y{t in T,D_,R[t]}, binary; # 1 if team T drafts player D with pick R
var tau{T,T}, binary; # 1 if trade occurs between team T and T
var Z; # linearization variable for maxmin
### adding synergy variables ###
var W{T,G_}; # number of players in group G_ on team T
var rho{U,T,G_} binary; # 1 if team T gets U players from group G_
var chiExp{T,G_}; # exponential linearization 
var chiLog{T,G_}; # logarithmic linearization


#### STACKELBERG DTF FORMULATION ##########################
maximize balanced_obj:
      sum{j in T, i_f in F, c in C[i_f]} v[c]*X[i_f,j,c]  
    + sum{i in T, id in D, c in C[id], r in R[i]} (v[c]/r)*Y[i,c,r]
    + sum{j in T, i_f in F, c in C[i_f]} z[c,j]*X[i_f,j,c]
    + Z
    + sum{i in T, g in G_} (1/b_synergy[g,g])*chiExp[i,g]
    + sum{i in T, g1 in G_, g2 in G_: g1 < g2} 
		(b_synergy[g1,g2])*(chiLog[i,g1]+chiLog[i,g2]); 
    

subject to

## cooperative ##
coop1 {j in T}: 
    Z <= sum{i in T, c in C[i]: i != j} v[c]*X[i,j,c]
         + sum{c in C[j]} v[c]*(1 - sum{i in T: i != j} X[j,i,c])
         + sum{i in T, c in S_ inter C[i]: i != j} vBar[c]*X[i,j,c]
         + sum{c in S_ inter C[j]} vBar[c]*(1 - sum{i in T: i != j} X[j,i,c]) 
         ;


## define W and linearize
defineW {j in T, g in G_}:
    W[j,g] == sum{i in T, c in C[i] inter G[g]: i != j} X[i,j,c]
    + sum{c in C[j] inter G[g]} (1 - sum{i in T: i != j} X[j,i,c])
    + sum{i_f in F, c in C[i_f] inter G[g]} X[i_f,j,c];


lin_1 {u in U, g in G_, i in T}: W[i,g] - u <= 15*(1-rho[u,i,g]);
lin_2 {u in U, g in G_, i in T}: W[i,g] - u >= -15*(1-rho[u,i,g]);
lin_3 {g in G_, i in T}: sum{u in U} rho[u,i,g] == 1;

lin_exp {g in G_, i in T}: chiExp[i,g] == sum{u in U} -exp(u)*rho[u,i,g];
lin_log {g in G_, i in T}: chiLog[i,g] == sum{u in U} log(u+1)*rho[u,i,g];


## all players assigned to at most one team ##
assign1 {i in N diff D, c in C[i]}: sum{j in T : j <> i} X[i,j,c] <= 1;

## players drafted at most once ##
draft1 {id in D, c in C[id]}: sum{i in T, r in R[i]} Y[i,c,r] <= 1;

## team draft once in each period ##
draft2 {i in T, r in R[i]}: sum{id in D, c in C[id]} Y[i,c,r] == 1;

## draftee accounting ##
#matchXY {id in D, c in C[id], j in T}: sum{r in R[j]} Y[j,c,r] = X[id,j,c];

## roster capacity ##
rosterCap {k in T}: 
    sum{i in N diff D, c in C[i]: i != k} X[i,k,c] 
    + sum{r in R[k], id in D, c in C[id]} Y[k,c,r]
    - sum{j in T, c in C[k]: j != k} X[k,j,c] <= pMax[k];

## budget capacity ##
budgetCap {k in T}: 
    sum{i in N diff D, c in C[i]: i != k} m[c]*X[i,k,c] 
    + sum{r in R[k], id in D, c in C[id]} m[c]*Y[k,c,r]
    - sum{j in T, c in C[k]: j != k} m[c]*X[k,j,c] <= b[k];
    
## value fairness ##
valFair1 {(i,j) in Arcs}: 
    sum{c in C[i]} v[c]*X[i,j,c] 
    - sum{c in C[j]} v[c]*X[j,i,c] >= -rv;
    
valFair2 {(i,j) in Arcs}: 
    sum{c in C[i]} v[c]*X[i,j,c] 
    - sum{c in C[j]} v[c]*X[j,i,c] <= rv;

## contract fairness ##
moneyFair1 {(i,j) in Arcs}: 
    sum{c in C[i]} m[c]*X[i,j,c] 
    - sum{c in C[j]} m[c]*X[j,i,c] >= -rm;
    
moneyFair2 {(i,j) in Arcs}: 
    sum{c in C[i]} m[c]*X[i,j,c] 
    - sum{c in C[j]} m[c]*X[j,i,c] <= rm;
    
## position limits ##
pos1 {k in T, p in P}: 
    sum{i in N diff D, c in Q[p] inter C[i]: i != k} X[i,k,c]
    + sum{r in R[k], id in D, c in C[id] inter Q[p]} Y[k,c,r]
    - sum{j in T, c in Q[p] inter C[k]: j != k} X[k,j,c] >= wL[k,p]; 
    

pos2 {k in T, p in P}: 
    sum{i in N diff D, c in Q[p] inter C[i]: i != k} X[i,k,c] 
    + sum{r in R[k], id in D, c in C[id] inter Q[p]} Y[k,c,r]
    - sum{j in T, c in Q[p] inter C[k]: j != k} X[k,j,c] <= wU[k,p]; 
    
## trades ##
fromTrade1 {(i,j) in Arcs}:
    tau[i,j] <= sum{c in C[i]} X[i,j,c];

fromTrade2 {(i,j) in Arcs}:
    sum{c in C[i]} X[i,j,c] <= M*tau[i,j];

toTrade1 {(i,j) in Arcs}:
    tau[i,j] <= sum{c in C[j]} X[j,i,c];

toTrade2 {(i,j) in Arcs}:
    sum{c in C[j]} X[j,i,c] <= M*tau[i,j];
    
## limit trades ##
limTrade {i in T}:
    sum{j in T, c in C[i]: j != i} X[i,j,c] <= ceil(0.2*card(C[i]));


##### OPTIONS #########################################
option omit_zero_rows 1;
option omit_zero_cols 1;







