// SVA for rotator, splitter, and top_module
// Bind these checkers to the DUT to verify reset, sequencing, and muxing behavior concisely.

//////////////////////////////////////////////////////////
// rotator checker
//////////////////////////////////////////////////////////
module rotator_sva(
  input logic        clk,
  input logic        reset,
  input logic        select,
  input logic [3:0]  data_in,
  input logic [3:0]  data_out
);
  default clocking cb @(posedge clk); endclocking

  // Reset drives zero on the following cycle
  property rot_rst_p;
    reset |=> (data_out == 4'h0);
  endproperty
  assert property(rot_rst_p);

  // Functional: one-bit left rotate every cycle out of reset
  property rot_rotate_p;
    (!reset && $past(!reset)) |=> (data_out == { $past(data_out)[2:0], $past(data_out)[3] });
  endproperty
  assert property(rot_rotate_p);

  // Coverage: exercise both select values and at least one update
  cover property (!reset ##1 select ##1 !select);
  cover property (!reset ##1 data_out == { $past(data_out)[2:0], $past(data_out)[3] });
endmodule

bind rotator rotator_sva rotator_sva_i(
  .clk(clk), .reset(reset), .select(select),
  .data_in(data_in), .data_out(data_out)
);

//////////////////////////////////////////////////////////
// splitter checker
//////////////////////////////////////////////////////////
module splitter_sva(
  input logic        clk,
  input logic        reset,
  input logic [7:0]  data_in,
  input logic [3:0]  data_out_lo,
  input logic [3:0]  data_out_hi
);
  default clocking cb @(posedge clk); endclocking

  // Reset drives zeros on the following cycle
  property spl_rst_p;
    reset |=> (data_out_lo == 4'h0 && data_out_hi == 4'h0);
  endproperty
  assert property(spl_rst_p);

  // Registered pass-through of slices (guard previous cycle not in reset)
  property spl_pass_p;
    (!reset && $past(!reset)) |-> (data_out_lo == $past(data_in[3:0]) &&
                                   data_out_hi == $past(data_in[7:4]));
  endproperty
  assert property(spl_pass_p);

  // Coverage: both halves see non-equal values at least once
  cover property (!reset && $past(!reset) &&
                  $past(data_in[7:4]) != $past(data_in[3:0]) |-> data_out_hi != data_out_lo);
endmodule

bind splitter splitter_sva splitter_sva_i(
  .clk(clk), .reset(reset), .data_in(data_in),
  .data_out_lo(data_out_lo), .data_out_hi(data_out_hi)
);

//////////////////////////////////////////////////////////
// top_module checker
//////////////////////////////////////////////////////////
module top_module_sva(
  input logic        clk,
  input logic        reset,
  input logic        select,
  input logic [7:0]  data_in,
  input logic [3:0]  data_out_lo,
  input logic [3:0]  data_out_hi,
  // internal wires from DUT scope (available to bind)
  input logic [3:0]  rotator_out,
  input logic [3:0]  splitter_out_lo,
  input logic [3:0]  splitter_out_hi
);
  default clocking cb @(posedge clk); endclocking

  // Golden model for rotator output (independent of select and inputs)
  logic [3:0] rot_exp;
  always_ff @(posedge clk) begin
    if (reset) rot_exp <= 4'h0;
    else       rot_exp <= {rot_exp[2:0], rot_exp[3]};
  end

  // Reset behavior
  property top_rst_p;
    reset |=> (data_out_lo == 4'h0 && data_out_hi == 4'h0);
  endproperty
  assert property(top_rst_p);

  // Internal rotator should match golden model
  property top_rot_matches_model_p;
    (!reset && $past(!reset)) |-> (rotator_out == rot_exp);
  endproperty
  assert property(top_rot_matches_model_p);

  // Select=1 path: both outputs take rotator_out (and equal each other)
  property top_sel1_p;
    (!reset && select) |=> (data_out_lo == $past(rotator_out) &&
                            data_out_hi == $past(rotator_out) &&
                            data_out_lo == data_out_hi);
  endproperty
  assert property(top_sel1_p);

  // Select=0 path: outputs take splitter slices
  property top_sel0_p;
    (!reset && !select) |=> (data_out_lo == $past(splitter_out_lo) &&
                             data_out_hi == $past(splitter_out_hi));
  endproperty
  assert property(top_sel0_p);

  // End-to-end check vs golden model on select=1 path
  property top_sel1_e2e_p;
    (!reset && select && $past(!reset)) |=> (data_out_lo == $past(rot_exp) &&
                                             data_out_hi == $past(rot_exp));
  endproperty
  assert property(top_sel1_e2e_p);

  // If splitter halves differ, top outputs must differ in select=0 path
  property top_sel0_diff_propagates_p;
    (!reset && !select && $past(!reset) &&
     ($past(splitter_out_lo) != $past(splitter_out_hi)))
    |=> (data_out_lo != data_out_hi);
  endproperty
  assert property(top_sel0_diff_propagates_p);

  // Coverage: exercise both top mux paths and a toggle
  cover property (!reset ##1 select ##1 !select ##1 select);
endmodule

bind top_module top_module_sva top_module_sva_i(
  .clk(clk), .reset(reset), .select(select), .data_in(data_in),
  .data_out_lo(data_out_lo), .data_out_hi(data_out_hi),
  .rotator_out(rotator_out),
  .splitter_out_lo(splitter_out_lo), .splitter_out_hi(splitter_out_hi)
);