// SVA checker for shift_register_counter
module shift_register_counter_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic        in,
  input  logic [3:0]  delay,
  input  logic [3:0]  q,

  // internal DUT signals (bind these)
  input  logic [3:0]  counter,
  input  logic [3:0]  shift_reg,
  input  logic [3:0]  delayed_out,
  input  logic [3:0]  counter_out
);

  default clocking cb @(posedge clk); endclocking
  // Assertions with explicit reset behavior
  // Synchronous reset drives flops to 0 on the same clock
  assert property (@cb reset |-> (counter == 4'd0 && shift_reg == 4'd0));
  assert property (@cb (reset && $past(reset)) |-> (counter == 4'd0 && shift_reg == 4'd0));

  // When not in reset (default disable), functional behavior
  default disable iff (reset);

  // Basic well-formedness
  assert property (@cb delay < 4 && !$isunknown(delay));                // legal variable index
  assert property (@cb !$isunknown({q, counter, shift_reg}));           // no X/Z on key state/outputs

  // Counter increments by 1 mod-16 when not in reset
  assert property (@cb counter == $past(counter) + 4'd1);

  // Shift register update
  assert property (@cb shift_reg == {$past(in), $past(shift_reg[3:1])});

  // Combinational outputs are consistent with internal nets
  assert property (@cb counter_out == counter);
  assert property (@cb delayed_out == shift_reg[delay]);
  assert property (@cb q == (delayed_out | counter_out));

  // Strong end-to-end delay mapping: shift_reg[j] holds in delayed by (4-j) cycles (after enough clean cycles)
  genvar j;
  generate
    for (j = 0; j < 4; j++) begin : g_delay_map
      localparam int D = 4 - j;
      assert property (@cb $past(!reset, D) |-> shift_reg[j] == $past(in, D));
    end
  endgenerate

  // Coverage
  // 1) Reset release
  cover property (@cb reset ##1 !reset);
  // 2) Exercise all legal delay values
  genvar v;
  generate
    for (v = 0; v < 4; v++) begin : g_cover_delay
      cover property (@cb !reset && delay == v[3:0]);
    end
  endgenerate
  // 3) Counter wrap-around
  cover property (@cb !reset && $past(counter) == 4'hF && counter == 4'h0);
  // 4) q activity
  cover property (@cb !reset && $changed(q));

endmodule

// Bind example (place in a testbench or a package included after the DUT is compiled):
// bind shift_register_counter shift_register_counter_sva i_shift_register_counter_sva (
//   .clk        (clk),
//   .reset      (reset),
//   .in         (in),
//   .delay      (delay),
//   .q          (q),
//   .counter    (counter),
//   .shift_reg  (shift_reg),
//   .delayed_out(delayed_out),
//   .counter_out(counter_out)
// );