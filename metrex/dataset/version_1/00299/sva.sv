// SVA for sky130_fd_sc_ls__a21boi
// Drop this inside the module or bind it externally.

`ifdef ASSERT_ON

// Functional equivalence (4-state safe, zero-delay)
assert property (@(A1 or A2 or B1_N) ##0 (Y === (B1_N & (~A1 | ~A2))));

// No-X on Y when inputs are known
assert property (@(A1 or A2 or B1_N) (!$isunknown({A1,A2,B1_N})) |-> ##0 (!$isunknown(Y)));

// Internal gate correctness (4-state safe, zero-delay)
assert property (@(B1_N)               ##0 (b           === ~B1_N));
assert property (@(A1 or A2)           ##0 (and0_out    === (A1 & A2)));
assert property (@(b or and0_out)      ##0 (nor0_out_Y  === ~(b | and0_out)));
assert property (@(nor0_out_Y)         ##0 (Y           === nor0_out_Y));

// Input space coverage (all 8 combinations)
cover property (@(A1 or A2 or B1_N) ##0 ({A1,A2,B1_N} == 3'b000));
cover property (@(A1 or A2 or B1_N) ##0 ({A1,A2,B1_N} == 3'b001));
cover property (@(A1 or A2 or B1_N) ##0 ({A1,A2,B1_N} == 3'b010));
cover property (@(A1 or A2 or B1_N) ##0 ({A1,A2,B1_N} == 3'b011));
cover property (@(A1 or A2 or B1_N) ##0 ({A1,A2,B1_N} == 3'b100));
cover property (@(A1 or A2 or B1_N) ##0 ({A1,A2,B1_N} == 3'b101));
cover property (@(A1 or A2 or B1_N) ##0 ({A1,A2,B1_N} == 3'b110));
cover property (@(A1 or A2 or B1_N) ##0 ({A1,A2,B1_N} == 3'b111));

// Output value/toggle coverage
cover property (@(A1 or A2 or B1_N) ##0 (Y == 1'b0));
cover property (@(A1 or A2 or B1_N) ##0 (Y == 1'b1));
cover property (@(A1 or A2 or B1_N) $rose(Y));
cover property (@(A1 or A2 or B1_N) $fell(Y));

`endif

// Optional bind examples (uncomment and place in a separate file if preferred):
// bind sky130_fd_sc_ls__a21boi sky130_fd_sc_ls__a21boi_sva_port (.Y(Y), .A1(A1), .A2(A2), .B1_N(B1_N));
// bind sky130_fd_sc_ls__a21boi sky130_fd_sc_ls__a21boi_sva_int  (.B1_N(B1_N), .b(b), .A1(A1), .A2(A2), .and0_out(and0_out), .nor0_out_Y(nor0_out_Y), .Y(Y));