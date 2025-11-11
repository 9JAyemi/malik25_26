// SVA for up_down_counter
// Bind this module to the DUT: bind up_down_counter up_down_counter_sva sva(.clk(clk), .reset(reset), .load(load), .direction(direction), .data_in(data_in), .count(count), .carry(carry));

module up_down_counter_sva (
  input logic        clk,
  input logic        reset,
  input logic        load,
  input logic        direction,
  input logic [7:0]  data_in,
  input logic [7:0]  count,
  input logic        carry
);

  default clocking cb @(posedge clk); endclocking

  // Sanity: no X/Z on key signals
  ap_no_x: assert property (!$isunknown({reset,load,direction,data_in,count,carry}));

  // Fundamental invariant: carry reflects count == 8'hFF (aligned due to identical pipelining)
  ap_carry_is_ff: assert property (carry == (count == 8'hFF));

  // Reset: next cycle outputs go to 0
  ap_reset_next_zero: assert property (reset |-> ##1 (count == 8'h00 && carry == 1'b0));

  // Load: next cycle outputs reflect data_in and its FF status
  ap_load_next: assert property (!reset && load |-> ##1 (count == data_in && carry == (data_in == 8'hFF)));

  // Count update: next cycle is +/- 1 modulo 256 when not reset/load
  ap_up_next:   assert property (!reset && !load &&  direction |-> ##1 count == (count + 8'h01));
  ap_down_next: assert property (!reset && !load && !direction |-> ##1 count == (count - 8'h01));

  // Optional consistency of carry on normal step (redundant with ap_carry_is_ff but localized to step)
  ap_carry_step: assert property (!reset && !load |-> ##1 carry == (count == 8'hFF));

  // Coverage
  cv_reset:        cover property (reset);
  cv_load_ff:      cover property (!reset && load && data_in == 8'hFF);
  cv_load_not_ff:  cover property (!reset && load && data_in != 8'hFF);
  cv_up_to_ff:     cover property (!reset && !load &&  direction && count == 8'hFE);
  cv_down_to_ff:   cover property (!reset && !load && !direction && count == 8'h00);
  cv_carry_high:   cover property (carry);

endmodule