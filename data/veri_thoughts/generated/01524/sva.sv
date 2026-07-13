module accumulator_sva
  #(parameter IWIDTH=16, OWIDTH=30)
  (
    input logic clk,
    input logic clear,
    input logic acc,
    input logic signed [IWIDTH-1:0] in,
    input logic signed [OWIDTH-1:0] out
  );

  // Clock: clk (posedge). No reset in RTL.
  // Logic: sequential reg out with combinational precompute.
  // Behavior: out_next = (clear ? 0 : out) + (acc ? signext(in) : 0).

  // Out updates exactly per the RTL next-state equation.
  check_update_equation: assert property (
    @(posedge clk)
      $past(1'b1,1,1'b0) |-> ( out == ( ($past(clear) ? '0 : $past(out)) + ($past(acc) ? $signed($past(in)) : '0) ) )
  );

  // When ~clear & ~acc, out holds its previous value.
  check_hold_when_idle: assert property (
    @(posedge clk)
      $past(1'b1,1,1'b0) && $past(!clear && !acc) |-> ( out == $past(out) )
  );

  // When clear & ~acc, out becomes zero.
  check_clear_without_acc_zeros: assert property (
    @(posedge clk)
      $past(1'b1,1,1'b0) && $past(clear && !acc) |-> ( out == '0 )
  );

  // When clear & acc, out loads sign-extended input.
  check_load_on_clear_and_acc: assert property (
    @(posedge clk)
      $past(1'b1,1,1'b0) && $past(clear && acc) |-> ( out == $signed($past(in)) )
  );

  // When ~clear & acc, out accumulates previous out plus sign-extended input.
  check_accumulate_adds_input: assert property (
    @(posedge clk)
      $past(1'b1,1,1'b0) && $past(!clear && acc) |-> ( out == $past(out) + $signed($past(in)) )
  );

  // If acc is 0, out ignores input and either holds or clears to zero.
  check_no_acc_behavior: assert property (
    @(posedge clk)
      $past(1'b1,1,1'b0) && $past(!acc) |-> ( out == ($past(clear) ? '0 : $past(out)) )
  );

  // If clear is 1, out ignores previous out and is either 0 or loads input.
  check_clear_behavior: assert property (
    @(posedge clk)
      $past(1'b1,1,1'b0) && $past(clear) |-> ( out == ($past(acc) ? $signed($past(in)) : '0) )
  );

  // Delta on accumulate equals the sign-extended input.
  check_delta_on_accumulate: assert property (
    @(posedge clk)
      $past(1'b1,1,1'b0) && $past(!clear && acc) |-> ( out - $past(out) == $signed($past(in)) )
  );

endmodule