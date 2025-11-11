// SVA for adder_shifter
// Bind this module to the DUT:  bind adder_shifter adder_shifter_sva sva_i (.*);

module adder_shifter_sva (
    input  logic [7:0] A,
    input  logic [7:0] B,
    input  logic       carry_in,
    input  logic       sub,
    input  logic [1:0] shift_amount,
    input  logic       shift_direction,
    input  logic [7:0] sum,
    input  logic       borrow_out,
    input  logic [7:0] shifted_output
);

  default clocking cb @(posedge $global_clock); endclocking

  // Reference expressions
  let sum9  = sub ? ({A,1'b0} - {B,1'b0} - carry_in)
                  : ({A,1'b0} + {B,1'b0} + carry_in);

  // Basic functional correctness
  assert property (sum == sum9[7:0]);
  assert property (borrow_out == sum9[8]);

  // Shift behavior (note: 0 = left, 1 = right; default => 0s)
  assert property ((shift_direction === 1'b0) |-> shifted_output == (sum9 << shift_amount)[7:0]);
  assert property ((shift_direction === 1'b1) |-> shifted_output == (sum9 >> shift_amount)[7:0]);
  assert property ((shift_direction !== 1'b0 && shift_direction !== 1'b1) |-> shifted_output == 8'b0);

  // Consistency when no shift
  assert property ((shift_amount == 2'd0) && (shift_direction === 1'b0 || shift_direction === 1'b1)
                   |-> shifted_output == sum);

  // Right shift by 1 propagates sum9[8] into MSB
  assert property ((shift_direction === 1'b1) && (shift_amount == 2'd1)
                   |-> shifted_output[7] == sum9[8]);

  // No X on outputs when inputs are known and shift_direction is 0/1
  assert property (!$isunknown({A,B,carry_in,sub,shift_amount}) &&
                   (shift_direction === 1'b0 || shift_direction === 1'b1)
                   |-> !$isunknown({sum,borrow_out,shifted_output}));

  // Coverage
  cover property (sub==1'b0 && sum9[8]==1'b1); // add with carry
  cover property (sub==1'b0 && sum9[8]==1'b0); // add no carry
  cover property (sub==1'b1 && sum9[8]==1'b1); // sub with borrow
  cover property (sub==1'b1 && sum9[8]==1'b0); // sub no borrow

  cover property (shift_direction==1'b0 && (shift_amount==2'd0));
  cover property (shift_direction==1'b0 && (shift_amount==2'd1));
  cover property (shift_direction==1'b0 && (shift_amount==2'd2));
  cover property (shift_direction==1'b0 && (shift_amount==2'd3));

  cover property (shift_direction==1'b1 && (shift_amount==2'd0));
  cover property (shift_direction==1'b1 && (shift_amount==2'd1));
  cover property (shift_direction==1'b1 && (shift_amount==2'd2));
  cover property (shift_direction==1'b1 && (shift_amount==2'd3));

  // Corner cases
  cover property (shift_direction==1'b1 && shift_amount==2'd1 && sum9[8]==1'b1); // MSB injection on right shift
  cover property (shift_direction==1'b0 && shift_amount!=2'd0 && sum9[8]==1'b1); // left shift with dropped bit8

endmodule

bind adder_shifter adder_shifter_sva sva_i (.*);