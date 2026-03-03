// SVA for mux_4to1_enable
// Bind into DUT; uses $global_clock to check combinational behavior race-free with ##0.

module mux_4to1_enable_sva (
  input  [3:0] in0,
  input  [3:0] in1,
  input  [3:0] in2,
  input  [3:0] in3,
  input  [1:0] sel,
  input        en,
  input  [3:0] out
);
  default clocking cb @(posedge $global_clock); endclocking

  // Functional equivalence (4-state aware) with same-timestep sampling
  a_func: assert property (1'b1 |-> ##0
    (out === ( en
               ? (sel==2'b00 ? in0
                : sel==2'b01 ? in1
                : sel==2'b10 ? in2
                : sel==2'b11 ? in3
                : 4'b0)
               : 4'b0 )));

  // en low forces zero (strong 4-state check)
  a_en0_zero: assert property ((!en) |-> ##0 (out === 4'b0));

  // Unknown sel takes default -> zero regardless of en
  a_sel_xz_zero: assert property ($isunknown(sel) |-> ##0 (out === 4'b0));

  // Per-select checks (explicit paths)
  a_s0: assert property ((en && sel==2'b00) |-> ##0 (out === in0));
  a_s1: assert property ((en && sel==2'b01) |-> ##0 (out === in1));
  a_s2: assert property ((en && sel==2'b10) |-> ##0 (out === in2));
  a_s3: assert property ((en && sel==2'b11) |-> ##0 (out === in3));

  // Minimal functional coverage (exercise all paths, including default)
  c_en0: cover property ((!en) && (out===4'b0));
  c_s0:  cover property ((en && sel==2'b00) && (out===in0));
  c_s1:  cover property ((en && sel==2'b01) && (out===in1));
  c_s2:  cover property ((en && sel==2'b10) && (out===in2));
  c_s3:  cover property ((en && sel==2'b11) && (out===in3));
  c_def: cover property ($isunknown(sel) && (out===4'b0));
endmodule

bind mux_4to1_enable mux_4to1_enable_sva sva_mux_4to1_enable (.*);