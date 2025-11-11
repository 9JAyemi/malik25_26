// SVA for module hyperbolic
// Concise checks of combinational relationships, X-prop, divide-by-zero behavior, and basic coverage.

module hyperbolic_sva (
  input  logic                     x,
  input  logic                     sineh_out,
  input  logic                     cosh_out,
  input  logic                     tanh_out,
  input  logic signed [31:0]       exp_x,
  input  logic signed [31:0]       exp_neg_x,
  input  logic signed [31:0]       exp_x_plus_exp_neg_x,
  input  logic signed [31:0]       sineh,
  input  logic signed [31:0]       cosh
);

  // Combinational consistency and X/Z guards
  always_comb begin
    // Input must be 0/1, not X/Z
    assert (!$isunknown(x)) else $error("hyperbolic: x is X/Z");

    // Internal relationships (as coded)
    assert (exp_x == $signed({{20{1'b0}}, x})) else $error("exp_x mismatch");
    assert (exp_neg_x == $signed({{20{1'b0}}, -x})) else $error("exp_neg_x mismatch");
    assert (exp_x_plus_exp_neg_x == exp_x + exp_neg_x) else $error("exp_x_plus_exp_neg_x mismatch");
    assert (sineh == exp_x - exp_neg_x) else $error("sineh mismatch");
    assert (cosh  == (exp_x_plus_exp_neg_x >> 1)) else $error("cosh mismatch");

    // Output truncation/LSB mapping (outputs are 1-bit)
    assert (sineh_out === (sineh >> 1)[0]) else $error("sineh_out LSB mismatch");
    assert (cosh_out  === (cosh  >> 1)[0]) else $error("cosh_out LSB mismatch");

    // Division behavior
    if (!$isunknown(cosh) && (cosh != 0))
      assert (tanh_out === (sineh / cosh)[0]) else $error("tanh_out mismatch when cosh!=0");
    else
      // Expect X on divide-by-zero or unknown denominator
      assert ($isunknown(tanh_out)) else $error("tanh_out must be X when cosh==0 or unknown");
  end

  // Minimal concurrent properties for truth-table sanity (captures subtle -x sizing effects)
  // Note: using x edges as sample event for this purely combinational DUT
  property p_x0;
    @(posedge x or negedge x)
      (!x && !$isunknown(x)) |->
        (exp_x == 0 && exp_neg_x == 0 &&
         sineh == 0 && cosh == 0 &&
         sineh_out === 1'b0 && cosh_out === 1'b0 &&
         $isunknown(tanh_out));
  endproperty
  assert property (p_x0) else $error("x=0 case violated");

  property p_x1;
    @(posedge x or negedge x)
      (x && !$isunknown(x)) |->
        (exp_x == 32'sd1 && exp_neg_x == 32'sd1 &&
         exp_x_plus_exp_neg_x == 32'sd2 &&
         sineh == 32'sd0 && cosh == 32'sd1 &&
         sineh_out === 1'b0 && cosh_out === 1'b0 &&
         tanh_out === 1'b0);
  endproperty
  assert property (p_x1) else $error("x=1 case violated");

  // Coverage
  cover property (@(posedge x or negedge x) (!x && !$isunknown(x))); // hit x=0
  cover property (@(posedge x or negedge x) ( x && !$isunknown(x))); // hit x=1
  cover property (@(posedge x or negedge x) (cosh == 0));            // divide-by-zero scenario observed
  cover property (@(posedge x or negedge x) (!$isunknown(cosh) && (cosh != 0) && (tanh_out === (sineh / cosh)[0]))); // valid divide case

endmodule

// Bind into DUT so internal nets are checked without modifying RTL behavior
bind hyperbolic hyperbolic_sva u_hyperbolic_sva (
  .x                        (x),
  .sineh_out                (sineh_out),
  .cosh_out                 (cosh_out),
  .tanh_out                 (tanh_out),
  .exp_x                    (exp_x),
  .exp_neg_x                (exp_neg_x),
  .exp_x_plus_exp_neg_x     (exp_x_plus_exp_neg_x),
  .sineh                    (sineh),
  .cosh                     (cosh)
);