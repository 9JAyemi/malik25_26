// SVA for shift_register
// Bindable monitor that checks reset, functional next-state behavior, and basic coverage.

module shift_register_sva (
  input logic        clock,
  input logic        reset,
  input logic        shift_left,
  input logic [3:0]  data_in,
  input logic [3:0]  data_out,
  input logic [3:0]  shift_reg
);
  default clocking cb @(posedge clock); endclocking

  // Static sanity: catch truncation in concatenations
  initial begin
    if ($bits({shift_reg[2:0], data_in}) != $bits(shift_reg))
      $warning("Truncation in left path: {shift_reg[2:0], data_in} -> 4b shift_reg (implemented behavior loads data_in)");
    if ($bits({data_in, shift_reg[3:1]}) != $bits(shift_reg))
      $warning("Truncation in right path: {data_in, shift_reg[3:1]} -> 4b shift_reg (implemented behavior shifts in data_in[0])");
  end

  // Reset clears register
  assert property (reset |=> (shift_reg == 4'b0));

  // Output mirrors internal state
  assert property (1'b1 |-> (data_out == shift_reg));

  // Functional behavior (as implemented by RTL)
  default disable iff (reset);
  // When shift_left=1, next state equals current data_in (due to truncation)
  assert property (shift_left |=> (shift_reg == $past(data_in)));
  // When shift_left=0, next state equals {data_in[0], prev shift_reg[3:1]}
  assert property (!shift_left |=> (shift_reg == {$past(data_in[0]), $past(shift_reg[3:1])}));

  // No X/Z on controls/state during operation
  assert property (!$isunknown(shift_left) && !$isunknown(data_in) &&
                   !$isunknown(shift_reg) && !$isunknown(data_out));

  // Coverage
  cover property (reset ##1 !reset);
  cover property (shift_left);
  cover property (!shift_left);
  cover property (shift_left ##1 !shift_left);
  cover property (!shift_left ##1 !shift_left);
endmodule

// Bind into DUT (connect internal shift_reg)
bind shift_register shift_register_sva u_shift_register_sva (
  .clock     (clock),
  .reset     (reset),
  .shift_left(shift_left),
  .data_in   (data_in),
  .data_out  (data_out),
  .shift_reg (shift_reg)
);