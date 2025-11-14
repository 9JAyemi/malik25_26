// SVA for CDR. Bind this into the DUT.
// Focus: correct edge detection, recovered clock behavior, and data sampling.

module CDR_sva (
  input  logic clk_ref,
  input  logic data_in,
  input  logic clk_out,
  input  logic data_out,

  // internal DUT signals (bound hierarchically)
  input  logic       data_in_delayed,
  input  logic [1:0] data_in_edge,
  input  logic       clk_out_delayed,
  input  logic       data_out_delayed
);

  // past-valid flags per domain
  logic pv_ref, pv_out;
  always @(posedge clk_ref) pv_ref <= 1'b1;
  always @(posedge clk_out) pv_out <= 1'b1;

  // 1) data_in_delayed samples data_in on clk_ref
  assert property (@(posedge clk_ref) disable iff (!pv_ref)
                   data_in_delayed == $past(data_in));

  // 2) Edge detection encoding correctness (given implementation math)
  //    stable -> 00, rise -> 11, fall -> 01; 10 should never occur.
  assert property (@(posedge clk_ref) disable iff (!pv_ref)
                   !$changed(data_in) |-> data_in_edge == 2'b00);
  assert property (@(posedge clk_ref) disable iff (!pv_ref)
                   $rose(data_in) |-> data_in_edge == 2'b11);
  assert property (@(posedge clk_ref) disable iff (!pv_ref)
                   $fell(data_in) |-> data_in_edge == 2'b01);
  assert property (@(posedge clk_ref) disable iff (!pv_ref)
                   data_in_edge != 2'b10);

  // 3) Recovered clock: toggle on any data edge; hold when no edge
  assert property (@(posedge clk_ref) disable iff (!pv_ref)
                   ($rose(data_in) or $fell(data_in)) |-> ##1 (clk_out == ~$past(clk_out)));
  assert property (@(posedge clk_ref) disable iff (!pv_ref)
                   !$changed(data_in) |-> ##1 (clk_out == $past(clk_out)));

  // 4) Outputs reflect internal regs
  assert property (@(posedge clk_ref) disable iff (!pv_ref) clk_out == clk_out_delayed);
  assert property (@(posedge clk_out) disable iff (!pv_out) data_out == data_out_delayed);

  // 5) Data_out captures data_in_delayed on clk_out edges
  //    Check at next clk_out edge the previous capture was correct.
  assert property (@(posedge clk_out) disable iff (!pv_out)
                   $past(data_out,1, posedge clk_out) == $past(data_in_delayed,1, posedge clk_out));

  // Coverage
  cover property (@(posedge clk_ref) $rose(data_in));
  cover property (@(posedge clk_ref) $fell(data_in));
  cover property (@(posedge clk_ref) ($rose(data_in) or $fell(data_in)) ##1 (clk_out != $past(clk_out)));
  cover property (@(posedge clk_out) data_out == 1'b0 ##1 data_out == 1'b1);

endmodule

// Bind into DUT (connects to internal signals)
bind CDR CDR_sva CDR_sva_i (
  .clk_ref(clk_ref),
  .data_in(data_in),
  .clk_out(clk_out),
  .data_out(data_out),
  .data_in_delayed(data_in_delayed),
  .data_in_edge(data_in_edge),
  .clk_out_delayed(clk_out_delayed),
  .data_out_delayed(data_out_delayed)
);