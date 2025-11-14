// SVA bind file for top_module and binary_ones_counter
// Focused, high-quality assertions + key coverage

module top_module_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic [3:0]  binary_num_reg,
  input  logic [2:0]  ones_count_reg,
  input  logic [3:0]  binary_number
);
  default clocking cb @(posedge clk); endclocking

  bit past_valid;
  always @(posedge clk) past_valid <= 1'b1;

  // No Xs once reset is low
  assert property (past_valid && !reset |-> !$isunknown({binary_num_reg, ones_count_reg, binary_number}));

  // binary_num_reg increments modulo 16 every cycle
  assert property (past_valid |-> (binary_num_reg == $past(binary_num_reg)+4'd1) ||
                                 ($past(binary_num_reg)==4'hF && binary_num_reg==4'h0));

  // binary_number is the max of previous-cycle regs (due to NBA ordering)
  assert property (past_valid |-> $past(binary_number) ==
                                  (($past(ones_count_reg) > $past(binary_num_reg)) ?
                                     $past(ones_count_reg) : $past(binary_num_reg)));

  // Coverage: wrap-around and both selection branches of max
  cover property (past_valid && ($past(binary_num_reg)==4'hF && binary_num_reg==4'h0));
  cover property (past_valid && ($past(ones_count_reg) >  $past(binary_num_reg)) &&
                               ($past(binary_number) == $past(ones_count_reg)));
  cover property (past_valid && ($past(ones_count_reg) <= $past(binary_num_reg)) &&
                               ($past(binary_number) == $past(binary_num_reg)));
  cover property (past_valid && ($past(ones_count_reg) == $past(binary_num_reg)));

  // Coverage: hit all 16 states of binary_num_reg
  cover property (binary_num_reg==4'h0);
  cover property (binary_num_reg==4'h1);
  cover property (binary_num_reg==4'h2);
  cover property (binary_num_reg==4'h3);
  cover property (binary_num_reg==4'h4);
  cover property (binary_num_reg==4'h5);
  cover property (binary_num_reg==4'h6);
  cover property (binary_num_reg==4'h7);
  cover property (binary_num_reg==4'h8);
  cover property (binary_num_reg==4'h9);
  cover property (binary_num_reg==4'hA);
  cover property (binary_num_reg==4'hB);
  cover property (binary_num_reg==4'hC);
  cover property (binary_num_reg==4'hD);
  cover property (binary_num_reg==4'hE);
  cover property (binary_num_reg==4'hF);
endmodule


module binary_ones_counter_sva (
  input  logic       clk,
  input  logic       reset,
  input  logic [3:0] binary_in,
  input  logic [2:0] ones_count
);
  default clocking cb @(posedge clk); endclocking

  // Asynchronous reset clears immediately and holds while asserted
  assert property (@(posedge reset) ones_count==3'd0);
  assert property (reset |-> ones_count==3'd0);

  // Output equals popcount of prior cycle's input (registered)
  assert property (!reset |-> ones_count == $countones($past(binary_in)));

  // Range and X checks
  assert property (!reset |-> ones_count <= 3'd4);
  assert property (!reset |-> !$isunknown(ones_count));

  // Coverage: exercise all popcount results 0..4
  cover property (!reset && ones_count==3'd0);
  cover property (!reset && ones_count==3'd1);
  cover property (!reset && ones_count==3'd2);
  cover property (!reset && ones_count==3'd3);
  cover property (!reset && ones_count==3'd4);

  // Coverage: reset pulse observed
  cover property (@(posedge clk) $rose(reset));
  cover property (@(posedge clk) $fell(reset));
endmodule


// Bind into DUTs
bind top_module           top_module_sva          u_top_sva  (.*);
bind binary_ones_counter  binary_ones_counter_sva u_cnt_sva  (.*);