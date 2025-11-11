// SVA for pipelined_booth_multiplier
// Focused, high-signal-coverage, concise checks and covers.

module pipelined_booth_multiplier_sva
(
  input  logic         clk,

  // DUT I/Os
  input  logic [15:0]  a,
  input  logic [15:0]  b,
  input  logic [31:0]  result,

  // DUT internals
  input  logic [7:0]   reg_file [0:7],
  input  logic [15:0]  a_reg,
  input  logic [15:0]  b_reg,
  input  logic [15:0]  shift_reg,
  input  logic [31:0]  product_reg,
  input  logic [3:0]   state,
  input  logic [1:0]   count,
  input  logic [15:0]  adder_input
);

  default clocking cb @(posedge clk); endclocking

  // Structural/static sanity checks (compile/elaboration-time)
  initial begin
    if ($bits(result) != 8 * $bits(reg_file[0]))
      $error("Width mismatch: result width (%0d) != sum of reg_file concat (%0d)",
             $bits(result), 8*$bits(reg_file[0]));
    if ($bits({a_reg[15], a_reg}) > $bits(adder_input))
      $error("Potential truncation: adder_input width (%0d) < concat width (%0d)",
             $bits(adder_input), $bits({a_reg[15], a_reg}));
    if ($bits({product_reg[31], product_reg[31:16]}) > $bits(product_reg))
      $error("Potential truncation: product_reg rotate RHS wider (%0d) than LHS (%0d)",
             $bits({product_reg[31], product_reg[31:16]}), $bits(product_reg));
  end

  // Helper
  function automatic bit is_stage4(logic [3:0] s);
    return !(s inside {4'd0,4'd1,4'd2});
  endfunction

  // Control/state integrity (no X/Z on key controls after first edge)
  bit seen_clk;
  always_ff @(posedge clk) seen_clk <= 1'b1;
  assert property (seen_clk |-> (! $isunknown(state) && ! $isunknown(count)));

  // State machine progression
  assert property (state == 4'd0 |=> state == 4'd1
                                     && count == 2'b01
                                     && a_reg == $past(a)
                                     && b_reg == $past(b)
                                     && shift_reg == $past(b));

  assert property (state == 4'd1 |=> state == 4'd2
                                     && shift_reg == {$past(shift_reg)[14], $past(shift_reg)}
                                     && count == ((($past(shift_reg)[15:14] == 2'b01)
                                                || ($past(shift_reg)[15:14] == 2'b10))
                                                  ? 2'b10 : 2'b01));

  assert property (state == 4'd2 |=> state == 4'd3
                                     && product_reg == {16'b0, $past(adder_input)} + $past(product_reg));

  // "Stage 4" (any state not 0/1/2)
  assert property (is_stage4(state) |=> (state inside {4'd0,4'd1})
                                        && count == $past(count) + 2'b01
                                        && reg_file[$past(count)] == $past(product_reg[7:0])
                                        && product_reg == {15'b0, $past(product_reg[31]), $past(product_reg[31:16])}
                                        && ((state == 4'd0) == ($past(count) == 2'b11)));

  // Combinational adder_input selection (as coded)
  assert property ((state == 4'd0) |-> adder_input == {a_reg[15], a_reg} - (b_reg << 1));
  assert property ((state == 4'd1) |-> adder_input == {a_reg[15], a_reg} + (b_reg << 1));
  assert property ((state == 4'd2) |-> adder_input == {a_reg[15], a_reg});
  assert property (is_stage4(state) |-> adder_input == 16'b0);

  // Result wiring correctness (matches reg_file concat as coded)
  assert property (1'b1 |-> result == {reg_file[7], reg_file[6], reg_file[5], reg_file[4],
                                       reg_file[3], reg_file[2], reg_file[1], reg_file[0]});

  // Coverage: exercise full pipeline loop 0->1->2->(stage4)->0
  cover property (state == 4'd0 ##1 state == 4'd1 ##1 state == 4'd2
                  ##1 is_stage4(state) ##1 state == 4'd0);

  // Coverage: both count decisions from state 1
  cover property (state == 4'd1 && $past(shift_reg)[15:14] inside {2'b01,2'b10}
                  |=> count == 2'b10);
  cover property (state == 4'd1 && !($past(shift_reg)[15:14] inside {2'b01,2'b10})
                  |=> count == 2'b01);

  // Coverage: all four reg_file indices 0..3 see a write in stage4
  cover property (is_stage4(state) && count == 2'b00);
  cover property (is_stage4(state) && count == 2'b01);
  cover property (is_stage4(state) && count == 2'b10);
  cover property (is_stage4(state) && count == 2'b11);

  // Optional end-to-end check: on completion (stage4 with count==3 -> next state 0), result should be stable with that write
  // Note: This checks the coded wiring; not algorithmic multiplication correctness.
  assert property (is_stage4(state) && count == 2'b11
                   |=> state == 4'd0
                    && result == {reg_file[7], reg_file[6], reg_file[5], reg_file[4],
                                  reg_file[3], reg_file[2], reg_file[1], reg_file[0]});

endmodule

// Bind into DUT
bind pipelined_booth_multiplier pipelined_booth_multiplier_sva
(
  .clk,
  .a,
  .b,
  .result,
  .reg_file,
  .a_reg,
  .b_reg,
  .shift_reg,
  .product_reg,
  .state,
  .count,
  .adder_input
);