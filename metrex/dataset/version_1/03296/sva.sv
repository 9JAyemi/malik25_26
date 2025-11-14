// SVA checkers and binds for pipelined_mux and mux2to1

// Checker for pipelined_mux
module pipelined_mux_sva_bind
(
  input  logic [7:0] in,
  input  logic [1:0] sel,
  input  logic [3:0] out,
  input  logic [3:0] stage1_out,
  input  logic [3:0] stage2_out
);
  default clocking cb @(*); endclocking

  // Stage-1 must zero-extend and select per sel[0] (default on X/Z -> in[5:4])
  ap_stage1_value: assert property (stage1_out === {2'b00,
                                  (sel[0]===1'b0) ? in[1:0] :
                                  (sel[0]===1'b1) ? in[3:2] :
                                                    in[5:4]});

  // Stage-2 must zero-extend and select per sel[1] (default on X/Z -> [3:2])
  ap_stage2_value: assert property (stage2_out === {2'b00,
                                  (sel[1]===1'b0) ? stage1_out[1:0] :
                                                    stage1_out[3:2]});

  // Output must mirror stage2
  ap_out_eq_stage2: assert property (out === stage2_out);

  // Direct end-to-end functional check (summarized)
  ap_out_func: assert property (out === {2'b00,
                           (sel[1]===1'b0) ? ((sel[0]===1'b0) ? in[1:0] :
                                              (sel[0]===1'b1) ? in[3:2] :
                                                                in[5:4])
                                           : 2'b00});

  // No X on out when inputs are 2-state
  ap_no_x_when_2state_in: assert property (!$isunknown({in,sel}) |-> !$isunknown(out));

  // Useful compact coverage
  // sel=00 -> out[1:0]=in[1:0]
  cp_00: cover property (sel===2'b00 && out[1:0]===in[1:0]);
  // sel=01 -> out[1:0]=in[3:2]
  cp_01: cover property (sel===2'b01 && out[1:0]===in[3:2]);
  // sel[1]=1 (or X/Z) -> out==0
  cp_sel1_1_or_x: cover property ((sel[1]!==1'b0) && out===4'b0000);
  // sel[0]=X/Z and sel[1]=0 -> default path to in[5:4]
  cp_sel0_x: cover property ($isunknown(sel[0]) && sel[1]===1'b0 && out[1:0]===in[5:4]);
  // sel[1]=X/Z -> default to upper slice -> out==0
  cp_sel1_x: cover property ($isunknown(sel[1]) && out===4'b0000);
endmodule

bind pipelined_mux pipelined_mux_sva_bind
  i_pipelined_mux_sva_bind(.in(in), .sel(sel), .out(out), .stage1_out(stage1_out), .stage2_out(stage2_out));


// Checker for mux2to1
module mux2to1_sva_bind
(
  input logic a,
  input logic b,
  input logic sel,
  input logic out
);
  default clocking cb @(*); endclocking

  // Functional equivalence
  ap_mux_func: assert property (out === (sel ? b : a));

  // No X on out when inputs are 2-state
  ap_no_x_when_2state_in: assert property (!$isunknown({a,b,sel}) |-> !$isunknown(out));

  // Coverage of both data paths and X-merge case
  cp_sel0: cover property (sel===1'b0);
  cp_sel1: cover property (sel===1'b1);
  cp_selx_merge: cover property ($isunknown(sel) && (a===b) && (out===a));
endmodule

bind mux2to1 mux2to1_sva_bind i_mux2to1_sva_bind(.a(a), .b(b), .sel(sel), .out(out));