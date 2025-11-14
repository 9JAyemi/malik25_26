// SVA for Ramifier: checks functional equivalence and provides concise coverage

`ifndef RAMIFIER_SVA_SV
`define RAMIFIER_SVA_SV

module Ramifier_sva #(
  parameter int BRANCH_CONDITION_WIDTH = 4
)(
  input  logic [BRANCH_CONDITION_WIDTH-1:0] condition,
  input  logic negative_flag,
  input  logic zero_flag,
  input  logic carry_flag,
  input  logic overflow_flag,
  input  logic take
);

  // Golden model of the combinational function
  function automatic logic exp_take(
    input logic [BRANCH_CONDITION_WIDTH-1:0] condition,
    input logic negative_flag, zero_flag, carry_flag, overflow_flag
  );
    case (condition)
      0:   exp_take = zero_flag;
      1:   exp_take = !zero_flag;
      2:   exp_take = carry_flag;
      3:   exp_take = !carry_flag;
      4:   exp_take = negative_flag;
      5:   exp_take = !negative_flag;
      6:   exp_take = overflow_flag;
      7:   exp_take = !overflow_flag;
      8:   exp_take = carry_flag && !zero_flag;
      9:   exp_take = !carry_flag || zero_flag;
      10:  exp_take = ~(negative_flag ^ overflow_flag); // XNOR
      11:  exp_take =  (negative_flag ^ overflow_flag);
      12:  exp_take = !zero_flag && ~(negative_flag ^ overflow_flag);
      13:  exp_take =  zero_flag ||  (negative_flag ^ overflow_flag);
      14:  exp_take = 1'b1;
      default: exp_take = 1'b0;
    endcase
  endfunction

  // Sample on any relevant input change; ##0 evaluates after combinational settle
  localparam int W = BRANCH_CONDITION_WIDTH;

  property p_equiv;
    @(condition or negative_flag or zero_flag or carry_flag or overflow_flag)
      1'b1 |-> ##0 (take === exp_take(condition, negative_flag, zero_flag, carry_flag, overflow_flag));
  endproperty
  assert property (p_equiv)
    else $error("Ramifier: take mismatch. cond=%0d z=%0b n=%0b c=%0b v=%0b take=%0b exp=%0b",
                condition, zero_flag, negative_flag, carry_flag, overflow_flag, take,
                exp_take(condition, negative_flag, zero_flag, carry_flag, overflow_flag));

  // If inputs are known, output must be known
  property p_no_x_out_when_inputs_known;
    @(condition or negative_flag or zero_flag or carry_flag or overflow_flag)
      !$isunknown({condition, negative_flag, zero_flag, carry_flag, overflow_flag})
      |-> ##0 !$isunknown(take);
  endproperty
  assert property (p_no_x_out_when_inputs_known)
    else $error("Ramifier: X/Z on take with known inputs. cond=%0d z/n/c/v=%0b%0b%0b%0b take=%0b",
                condition, zero_flag, negative_flag, carry_flag, overflow_flag, take);

  // Functional coverage: see each encoded condition, and both outcomes where attainable
  genvar i;
  generate
    for (i=0; i<=14; i++) begin : gen_cov
      cover property (@(condition or negative_flag or zero_flag or carry_flag or overflow_flag)
                      (condition == i));
      cover property (@(condition or negative_flag or zero_flag or carry_flag or overflow_flag)
                      (condition == i) && ##0 (take && exp_take(condition, negative_flag, zero_flag, carry_flag, overflow_flag)));
      cover property (@(condition or negative_flag or zero_flag or carry_flag or overflow_flag)
                      (condition == i) && ##0 (!take && !exp_take(condition, negative_flag, zero_flag, carry_flag, overflow_flag)));
    end
    // Default branch observed
    cover property (@(condition)
                    !(condition inside {0,1,2,3,4,5,6,7,8,9,10,11,12,13,14}));
  endgenerate

endmodule

// Bind into the DUT
bind Ramifier Ramifier_sva #(.BRANCH_CONDITION_WIDTH(BRANCH_CONDITION_WIDTH)) Ramifier_sva_i (
  .condition(condition),
  .negative_flag(negative_flag),
  .zero_flag(zero_flag),
  .carry_flag(carry_flag),
  .overflow_flag(overflow_flag),
  .take(take)
);

`endif