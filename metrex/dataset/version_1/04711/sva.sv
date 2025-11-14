// SystemVerilog Assertions for xor_48_salt
// Place inside the module or bind externally. Concise, high-signal-coverage.

`ifndef X48_SALT_SVA
`define X48_SALT_SVA
// synopsys translate_off
// pragma translate_off

default clocking cb @(posedge CLK); endclocking

// Spec recomputation of Xtmp (bitwise salt/mux)
let S      = Y[59:48];
let upper  = ((~S & X[47:36]) | (S & X[23:12]));
let lower  = ((~S & X[23:12]) | (S & X[47:36]));
let xtmp_s = {upper, X[35:24], lower, X[11:0]};

// 1) Combinational correctness of Xtmp (full vector)
assert property (Xtmp == xtmp_s);

// 2) Registered XOR timing/functional correctness (1-cycle latency)
assert property ($past(1'b1) |-> Dout == $past(xtmp_s ^ Y[47:0]));

// 3) Output is known when prior-cycle inputs are known
assert property ($past(!$isunknown({X,Y})) |-> !$isunknown(Dout));

// 4) If inputs hold steady, output holds steady
assert property ($past(1'b1) && $stable({X,Y}) |-> $stable(Dout));

// Coverage: exercise salt select and XOR masks
cover property ($past(1'b1) && $past(S == 12'h000)); // all select=0
cover property ($past(1'b1) && $past(S == 12'hFFF)); // all select=1
cover property ((|S) && (|~S) && (|(X[47:36]^X[23:12]))); // mixed select with differing sources
cover property ($past(1'b1) && $past(Y[47:0] == 48'h0)); // XOR mask = 0
cover property ($past(1'b1) && $past(Y[47:0] == 48'hFFFF_FFFF_FFFF)); // XOR mask = all 1s

// pragma translate_on
// synopsys translate_on
`endif