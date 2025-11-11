// SVA for shift_register
// Notes: As coded, a shift when reset=0 loads out <= in (the concat truncates).
// Bind this module to the DUT for checks and coverage.

module shift_register_sva #(parameter WIDTH=8)
(
  input logic                clk,
  input logic                reset,
  input logic                shift,
  input logic [WIDTH-1:0]    in,
  input logic [WIDTH-1:0]    out
);

  default clocking cb @(posedge clk); endclocking

  // Track availability of a $past() sample on clk
  logic past_v;
  always_ff @(posedge clk or posedge reset) begin
    if (reset) past_v <= 1'b0;
    else       past_v <= 1'b1;
  end

  // Asynchronous reset effects
  // Out goes to zero immediately on reset assertion and stays zero while reset=1
  assert property (@(posedge reset) out == '0)
    else $error("out not zero on posedge reset");

  assert property (reset |-> out == '0)
    else $error("out not held at zero during reset");

  // Functional behavior on clk edges (when not in reset)
  // Hold when shift=0
  assert property (past_v && !reset && !shift |=> out == $past(out))
    else $error("out changed without shift");

  // Update when shift=1 (as coded, out loads in)
  assert property (past_v && !reset && shift |=> out == $past(in))
    else $error("out did not load input on shift");

  // Output changes only if shift was asserted (outside reset)
  assert property (past_v && !reset && (out != $past(out)) |-> $past(shift))
    else $error("out changed without prior shift");

  // Basic X/Z sanitation after reset deasserted
  assert property (!reset |-> !$isunknown(out))
    else $error("out is X/Z when not in reset");

  // Coverage
  cover property (@(posedge reset) 1);                  // reset seen
  cover property (!reset && shift);                     // a shift occurs
  cover property (!reset && !shift);                    // a hold cycle occurs
  cover property (past_v && !reset && shift [*2]);      // two consecutive shifts
  cover property ($fell(reset) ##1 shift);              // shift right after reset release

endmodule

// Bind into the DUT
bind shift_register shift_register_sva #(.WIDTH(8)) u_shift_register_sva (
  .clk   (clk),
  .reset (reset),
  .shift (shift),
  .in    (in),
  .out   (out)
);