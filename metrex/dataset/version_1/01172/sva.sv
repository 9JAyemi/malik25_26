// SVA for add_sub_shift + submodules
// Assumes a simulation clock/reset are available as clk, rst_n.
// Bind as needed from your TB.

// Reference model (golden) for the barrel shifter behavior:
// DIR==1: right shift A by AMT; MSBs filled from B[AMT-1:0].
// DIR==0: left  shift A by AMT; LSBs filled from B[3:3-AMT+1].
// fill encodes {unused B bits, spilled A bits} for the chosen DIR.
package add_sub_shift_ref_pkg;
  function automatic logic [3:0] ref_shift_q(input logic [3:0] A, B,
                                             input logic DIR,
                                             input logic [1:0] AMT);
    unique case (AMT)
      2'd0: ref_shift_q = A;
      2'd1: ref_shift_q = DIR ? {B[0],      A[3:1]} : {A[2:0],      B[3]};
      2'd2: ref_shift_q = DIR ? {B[1:0],    A[3:2]} : {A[1:0],    B[3:2]};
      2'd3: ref_shift_q = DIR ? {B[2:0],    A[3]}   : {A[0],      B[3:1]};
      default: ref_shift_q = 'x;
    endcase
  endfunction

  function automatic logic [3:0] ref_shift_fill(input logic [3:0] A, B,
                                                input logic DIR,
                                                input logic [1:0] AMT);
    unique case (AMT)
      2'd0: ref_shift_fill = DIR ? B : A;
      2'd1: ref_shift_fill = DIR ? {B[3:1], A[0]}   : {A[3],   B[0]};
      2'd2: ref_shift_fill = DIR ? {B[3:2], A[1:0]} : {A[3:2], B[1:0]};
      2'd3: ref_shift_fill = DIR ? {B[3],   A[2:0]} : {A[3:1], B[2:0]};
      default: ref_shift_fill = 'x;
    endcase
  endfunction
endpackage

import add_sub_shift_ref_pkg::*;

// Checker for barrel_shifter
module barrel_shifter_sva
(
  input logic clk, rst_n,
  input logic [3:0] A, B,
  input logic DIR,
  input logic [1:0] AMT,
  input logic [3:0] Q,
  input logic [3:0] fill
);
  // No-X on controls and inputs
  assert property (@(posedge clk) disable iff (!rst_n)
    !$isunknown({A,B,DIR,AMT}));

  // Functional correctness vs golden model
  assert property (@(posedge clk) disable iff (!rst_n)
    Q == ref_shift_q(A,B,DIR,AMT));

  assert property (@(posedge clk) disable iff (!rst_n)
    fill == ref_shift_fill(A,B,DIR,AMT));

  // Coverage: exercise all DIR/AMT combos
  genvar i;
  for (i=0;i<4;i++) begin : g_cov_amt
    cover property (@(posedge clk) disable iff (!rst_n)
      AMT==i[1:0] && DIR==0);
    cover property (@(posedge clk) disable iff (!rst_n)
      AMT==i[1:0] && DIR==1);
  end
endmodule

// Checker for adder_subtractor
module adder_subtractor_sva
(
  input logic clk, rst_n,
  input logic [3:0] A, B,
  input logic mode,
  input logic [3:0] Q
);
  assert property (@(posedge clk) disable iff (!rst_n)
    !$isunknown({A,B,mode}));

  assert property (@(posedge clk) disable iff (!rst_n)
    Q == (mode ? (A - B) : (A + B)));

  // Cover wrap-around on add and borrow on sub (4-bit saturation behavior)
  cover property (@(posedge clk) disable iff (!rst_n)
    mode==0 && B!=0 && ((A + B) < A));
  cover property (@(posedge clk) disable iff (!rst_n)
    mode==1 && B!=0 && ((A - B) > A));
endmodule

// Top-level end-to-end checker for add_sub_shift
module add_sub_shift_sva
(
  input logic clk, rst_n,
  input logic [3:0] A, B,
  input logic mode,
  input logic DIR,
  input logic [1:0] AMT,
  input logic [3:0] Q
);
  logic [3:0] sA, sB;
  assign sA = ref_shift_q(A,B,DIR,AMT);
  assign sB = ref_shift_fill(A,B,DIR,AMT);

  assert property (@(posedge clk) disable iff (!rst_n)
    !$isunknown({A,B,mode,DIR,AMT}));

  // End-to-end: output equals add/sub of shifted operands
  assert property (@(posedge clk) disable iff (!rst_n)
    Q == (mode ? (sA - sB) : (sA + sB)));

  // Basic scenario coverage
  cover property (@(posedge clk) disable iff (!rst_n)
    mode==0 && DIR==0 && AMT==2'd0);
  cover property (@(posedge clk) disable iff (!rst_n)
    mode==0 && DIR==1 && AMT==2'd3);
  cover property (@(posedge clk) disable iff (!rst_n)
    mode==1 && DIR==0 && AMT==2'd1);
  cover property (@(posedge clk) disable iff (!rst_n)
    mode==1 && DIR==1 && AMT==2'd2);

  // Corner data patterns
  cover property (@(posedge clk) disable iff (!rst_n)
    A==4'h0 && B==4'hF);
  cover property (@(posedge clk) disable iff (!rst_n)
    A==4'hF && B==4'h0);
endmodule

// Example binds (adjust clk/rst_n paths as needed)
// bind barrel_shifter     barrel_shifter_sva     bs_sva (.*);
// bind adder_subtractor   adder_subtractor_sva   as_sva (.*);
// bind add_sub_shift      add_sub_shift_sva      top_sva (.*);