// SVA for top_module
module top_module_sva (
  input logic               clk,
  // DUT ports
  input logic [255:0]       in0,
  input logic [7:0]         sel0,
  input logic [255:0]       in1,
  input logic [7:0]         sel1,
  input logic               select,
  input logic [7:0]         sum,
  // DUT internals
  input logic [255:0]       mux_in,
  input logic [7:0]         mux_sel,
  input logic               mux_out0,
  input logic               mux_out1,
  input logic [3:0]         adder_in0,
  input logic [3:0]         adder_in1
);

  // clocking and past-valid
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!past_valid);

  // Basic X-checks on key controls/outputs
  assert property (!$isunknown({select, sel0, sel1, mux_sel})); // no X/Z on controls
  assert property (!$isunknown({mux_out0, mux_out1, sum}));     // no X/Z on primary outputs

  // Registered mux input selection (1-cycle latency from select decision)
  assert property (mux_in  == $past(select ? in1  : in0));
  assert property (mux_sel == $past(select ? sel1 : sel0));

  // 256:1 mux correctness
  assert property (mux_out0 == mux_in[mux_sel]);
  assert property (mux_out1 == in1[sel1]);

  // Registered replication into adder inputs (1-cycle after mux_outs)
  assert property (adder_in0 == {4{$past(mux_out0)}});
  assert property (adder_in1 == {4{$past(mux_out1)}});
  // Domain check: replicated form must be 0000 or FFFF
  assert property (adder_in0 inside {4'h0, 4'hF});
  assert property (adder_in1 inside {4'h0, 4'hF});

  // Adder correctness: sum encodes 5-bit a+b in [7:3] and zeros in [2:0]
  assert property ({sum[7], sum[6:3]} == ({1'b0, adder_in0} + {1'b0, adder_in1}));
  assert property (sum[2:0] == 3'b000);

  // End-to-end pipeline check (optional but strong): sum derived from last-cycle mux_outs
  assert property ({sum[7], sum[6:3]} ==
                   ({1'b0, {4{$past(mux_out0)}}} + {1'b0, {4{$past(mux_out1)}}}));

  // Functional coverage
  // Exercise both select paths and boundary selects
  cover property ($rose(select));
  cover property ($fell(select));
  cover property (sel0 == 8'h00);
  cover property (sel0 == 8'hFF);
  cover property (sel1 == 8'h00);
  cover property (sel1 == 8'hFF);

  // Cover both values on mux outputs
  cover property (mux_out0 == 1'b0);
  cover property (mux_out0 == 1'b1);
  cover property (mux_out1 == 1'b0);
  cover property (mux_out1 == 1'b1);

  // Cover both mux0 data paths with consistent registered inputs
  cover property ($past(select==1'b0) && mux_sel == $past(sel0) && mux_in == $past(in0)
                  && mux_out0 == mux_in[mux_sel]);
  cover property ($past(select==1'b1) && mux_sel == $past(sel1) && mux_in == $past(in1)
                  && mux_out0 == mux_in[mux_sel]);

  // Cover adder result space implied by design: 0, 15<<3 (=0x78), 30<<3 (=0xF0)
  cover property (sum == 8'h00);
  cover property (sum == 8'h78);
  cover property (sum == 8'hF0);

endmodule

// Bind into DUT
bind top_module top_module_sva sva_i (
  .clk      (clk),
  .in0      (in0),
  .sel0     (sel0),
  .in1      (in1),
  .sel1     (sel1),
  .select   (select),
  .sum      (sum),
  .mux_in   (mux_in),
  .mux_sel  (mux_sel),
  .mux_out0 (mux_out0),
  .mux_out1 (mux_out1),
  .adder_in0(adder_in0),
  .adder_in1(adder_in1)
);