// SystemVerilog Assertions for FSM_Convert_Fixed_To_Float
// Put inside the module (recommended) or bind to it. Focused, high-quality checks and coverage.

`ifdef ASSERT_ON
// Clocking and reset controls
default clocking cb @(posedge CLK); endclocking
default disable iff (RST_FF)

localparam [7:0] ENCD_1A = 8'h1A;

// Basic sanity: no X on key nets after reset released
assert property (!$isunknown({state_reg, EN_REG1, EN_REGmult, EN_REG2, LOAD, ACK_FF, EN_MS_1, MS_1, RST})) else $error("X detected");

// State encoding must be legal
assert property (state_reg inside {a,b,c,d,e,f,g,h,i,j,k}) else $error("Illegal state");

// Asynchronous reset behavior
assert property (@(posedge RST_FF) state_reg == a) else $error("Async reset failed to go to state a");
assert property (@(posedge CLK) RST_FF |-> state_reg == a) else $error("State not a while reset asserted");

// Deterministic next-state transitions (no reset)
assert property (state_reg==a && !Begin_FSM_FF |=> state_reg==a) else $error("a should hold when Begin_FSM_FF=0");
assert property (state_reg==a &&  Begin_FSM_FF |=> state_reg==b) else $error("a->b on begin");
assert property (state_reg==b |=> state_reg==c) else $error("b->c");
assert property (state_reg==c |=> state_reg==d) else $error("c->d");
assert property (state_reg==d |=> state_reg==e) else $error("d->e");
assert property (state_reg==e && (Encd==ENCD_1A) |=> state_reg==k) else $error("e->k on Encd==1A");
assert property (state_reg==e && (Encd!=ENCD_1A) |=> state_reg==f) else $error("e->f on Encd!=1A");
assert property (state_reg==f |=> state_reg==g) else $error("f->g");
assert property (state_reg==g |=> state_reg==h) else $error("g->h");
assert property (state_reg==h |=> state_reg==i) else $error("h->i");
assert property (state_reg==i |=> state_reg==j) else $error("i->j");
assert property (state_reg==j |=> state_reg==j) else $error("j should hold");
assert property (state_reg==k |=> state_reg==h) else $error("k->h");

// Output decode for each state
assert property (state_reg==a && !Begin_FSM_FF |-> !EN_REG1 && !EN_REGmult && !EN_REG2 && !LOAD && !ACK_FF && !EN_MS_1 && !MS_1 && !RST);
assert property (state_reg==a &&  Begin_FSM_FF |->  RST    && !EN_REG1    && !EN_REGmult && !EN_REG2 && !LOAD && !ACK_FF && !EN_MS_1 && !MS_1);

assert property (state_reg==b |-> EN_REG1 && !EN_REGmult && !EN_REG2 && !LOAD && !ACK_FF && !EN_MS_1 && !MS_1 && !RST);
assert property (state_reg==c |-> !EN_REG1 && !EN_REGmult && !EN_REG2 && !LOAD && !ACK_FF && !EN_MS_1 && !MS_1 && !RST);
assert property (state_reg==d |-> EN_REGmult && !EN_REG1 && !EN_REG2 && !LOAD && !ACK_FF && !EN_MS_1 && !MS_1 && !RST);
assert property (state_reg==e |-> EN_MS_1 && !EN_REG1 && !EN_REGmult && !EN_REG2 && !LOAD && !ACK_FF && !MS_1 && !RST);
assert property (state_reg==f |-> EN_MS_1 && MS_1 && !EN_REG1 && !EN_REGmult && !EN_REG2 && !LOAD && !ACK_FF && !RST);
assert property (state_reg==g |-> !EN_REG1 && !EN_REGmult && !EN_REG2 && !LOAD && !ACK_FF && !EN_MS_1 && !MS_1 && !RST);
assert property (state_reg==h |-> LOAD && !EN_REG1 && !EN_REGmult && !EN_REG2 && !ACK_FF && !EN_MS_1 && !MS_1 && !RST);
assert property (state_reg==i |-> EN_REG2 && !EN_REG1 && !EN_REGmult && !LOAD && !ACK_FF && !EN_MS_1 && !MS_1 && !RST);
assert property (state_reg==j |-> ACK_FF && !EN_REG1 && !EN_REGmult && !EN_REG2 && !LOAD && !EN_MS_1 && !MS_1 && !RST);
assert property (state_reg==k |-> !EN_REG1 && !EN_REGmult && !EN_REG2 && !LOAD && !ACK_FF && !EN_MS_1 && !MS_1 && !RST);

// Output implies state (and consistency)
assert property (EN_REG1   |-> state_reg==b);
assert property (EN_REGmult|-> state_reg==d);
assert property (EN_REG2   |-> state_reg==i);
assert property (LOAD      |-> state_reg==h);
assert property (ACK_FF    |-> state_reg==j);
assert property (MS_1      |-> state_reg==f && EN_MS_1);
assert property (EN_MS_1   |-> state_reg inside {e,f});

// Structural one-hot0 among primary enables (EN_MS_1/MS_1/RST are excluded by design)
assert property ($onehot0({EN_REG1, EN_REGmult, EN_REG2, LOAD, ACK_FF}));

// Pulse-width expectations
assert property (EN_REG1   |=> !EN_REG1);
assert property (EN_REGmult|=> !EN_REGmult);
assert property (EN_REG2   |=> !EN_REG2);
assert property (LOAD      |=> !LOAD);
assert property (MS_1      |=> !MS_1);

// EN_MS_1 length per path out of e
assert property (state_reg==e && Encd!=ENCD_1A |=> EN_MS_1 ##1 EN_MS_1 ##1 !EN_MS_1);
assert property (state_reg==e && Encd==ENCD_1A |=> !EN_MS_1);

// RST output only in a when Begin_FSM_FF
assert property (RST |-> state_reg==a && Begin_FSM_FF);
assert property (state_reg==a && Begin_FSM_FF |-> RST);

// Functional coverage: both trajectories reach ACK_FF
sequence seq_norm;
  (state_reg==a && Begin_FSM_FF)
  ##1 (state_reg==b)
  ##1 (state_reg==c)
  ##1 (state_reg==d)
  ##1 (state_reg==e && Encd!=ENCD_1A)
  ##1 (state_reg==f)
  ##1 (state_reg==g)
  ##1 (state_reg==h)
  ##1 (state_reg==i)
  ##1 (state_reg==j);
endsequence
cover property (seq_norm);

sequence seq_short;
  (state_reg==a && Begin_FSM_FF)
  ##1 (state_reg==b)
  ##1 (state_reg==c)
  ##1 (state_reg==d)
  ##1 (state_reg==e && Encd==ENCD_1A)
  ##1 (state_reg==k)
  ##1 (state_reg==h)
  ##1 (state_reg==i)
  ##1 (state_reg==j);
endsequence
cover property (seq_short);

// Cover: all states seen
cover property (state_reg inside {a,b,c,d,e,f,g,h,i,j,k});

`endif