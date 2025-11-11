// SVA checkers for add_sub_and and its submodules.
// Concise, end-to-end and per-block checks with key functional coverage.

module add_sub_and_sva #(parameter int W=8)
(
  input  logic [W-1:0] in1,
  input  logic [W-1:0] in2,
  input  logic         ctrl,
  input  logic [W-1:0] out,
  input  logic [W-1:0] out_and
);
  default clocking cb @(in1 or in2 or ctrl or out or out_and); endclocking

  // helpers
  let sum9 = {1'b0,in1} + {1'b0,in2};
  let sum8 = sum9[W-1:0];

  // No X on outputs when inputs are known
  a_no_x: assert property (@cb disable iff ($isunknown({in1,in2,ctrl}))
                           !$isunknown({out,out_and}));

  // Top-level functionality
  a_and_ok:  assert property (@cb disable iff ($isunknown({in1,in2}))
                              out_and == (in1 & in2));
  // Given this design, ctrl==1 forces add_in=in2 and subtraction, so out==0
  a_add_ok:  assert property (@cb disable iff ($isunknown({in1,in2,ctrl}))
                              out == (ctrl ? '0 : sum8));

  // Combinational: outputs only change when inputs change
  a_no_spurious: assert property (@cb $changed({out,out_and}) |-> $changed({in1,in2,ctrl}));

  // Functional coverage
  c_ctrl0:        cover property (@cb ctrl==0);
  c_ctrl1_zero:   cover property (@cb ctrl==1 && out=='0);
  c_add_overflow: cover property (@cb (ctrl==0) && sum9[W]); // overflow on addition
  c_ctrl_rise:    cover property (@cb $rose(ctrl));
  c_ctrl_fall:    cover property (@cb $fell(ctrl));
  c_and_zero:     cover property (@cb out_and=='0);
  c_and_ones:     cover property (@cb out_and=={W{1'b1}});

endmodule


module mux2to1_sva #(parameter int W=8)
(
  input  logic [W-1:0] in0,
  input  logic [W-1:0] in1,
  input  logic         sel,
  input  logic [W-1:0] out
);
  default clocking cb @(in0 or in1 or sel or out); endclocking

  a_mux_ok:       assert property (@cb disable iff($isunknown({in0,in1,sel}))
                                   out == (sel ? in1 : in0));
  a_no_spurious:  assert property (@cb $changed(out) |-> $changed({in0,in1,sel}));

  c_sel0:         cover property (@cb sel==0 && out==in0);
  c_sel1:         cover property (@cb sel==1 && out==in1);
  c_sel_rise:     cover property (@cb $rose(sel));
  c_sel_fall:     cover property (@cb $fell(sel));

endmodule


module adder8_sva #(parameter int W=8)
(
  input  logic [W-1:0] in1,
  input  logic [W-1:0] in2,
  input  logic         sub,
  input  logic [W-1:0] out
);
  default clocking cb @(in1 or in2 or sub or out); endclocking

  let sum9  = {1'b0,in1} + {1'b0,in2};
  let diff9 = {1'b0,in1} - {1'b0,in2};
  let sum8  = sum9[W-1:0];
  let diff8 = diff9[W-1:0];

  a_addsub_ok:    assert property (@cb disable iff($isunknown({in1,in2,sub}))
                                   out == (sub ? diff8 : sum8));
  a_no_spurious:  assert property (@cb $changed(out) |-> $changed({in1,in2,sub}));

  c_add_mode:     cover property (@cb sub==0);
  c_sub_mode:     cover property (@cb sub==1);
  c_add_overflow: cover property (@cb (sub==0) && sum9[W]);
  c_sub_borrow:   cover property (@cb (sub==1) && diff9[W]); // negative result

endmodule


module and8_sva #(parameter int W=8)
(
  input  logic [W-1:0] in1,
  input  logic [W-1:0] in2,
  input  logic [W-1:0] out
);
  default clocking cb @(in1 or in2 or out); endclocking

  a_and_ok:       assert property (@cb disable iff($isunknown({in1,in2}))
                                   out == (in1 & in2));
  a_no_spurious:  assert property (@cb $changed(out) |-> $changed({in1,in2}));

  c_zero:         cover property (@cb out=='0);
  c_all_ones:     cover property (@cb out=={W{1'b1}});

endmodule


// Bind these checkers to the DUT and submodules
bind add_sub_and add_sub_and_sva #(.W(8)) add_sub_and_sva_i (.*);
bind mux2to1     mux2to1_sva     #(.W(8)) mux2to1_sva_i     (.*);
bind adder8      adder8_sva      #(.W(8)) adder8_sva_i      (.*);
bind and8        and8_sva        #(.W(8)) and8_sva_i        (.*);