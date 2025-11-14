// SVA for binary_add_sub
// Bind this checker to the DUT to verify arithmetic correctness, carry-chain, and storage behavior.
module binary_add_sub_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic [31:0] a,
  input  logic [31:0] b,
  input  logic        sub,
  input  logic        enable,
  input  logic [31:0] sum,

  // Internal DUT signals bound in
  input  logic [31:0] result,
  input  logic [31:0] inverted_b,
  input  logic [31:0] g,
  input  logic [31:0] p,
  input  logic [31:0] c,
  input  logic [7:0]  stored_num
);

  function automatic [31:0] inv_b(input logic        sub_f,
                                  input logic [31:0] b_f);
    inv_b = sub_f ? (~b_f + 32'd1) : b_f;
  endfunction

  function automatic [31:0] carry_exp(input logic        sub_f,
                                      input logic [31:0] a_f,
                                      input logic [31:0] b_f);
    logic [31:0] ib, cf;
    int i;
    begin
      ib     = inv_b(sub_f, b_f);
      cf[0]  = sub_f;
      for (i = 1; i < 32; i++) begin
        cf[i] = (a_f[i-1] & ib[i-1]) | ((a_f[i-1] ^ ib[i-1]) & cf[i-1]);
      end
      carry_exp = cf;
    end
  endfunction

  // Arithmetic correctness (functional)
  assert property (@(posedge clk) disable iff (reset)
    inverted_b == inv_b(sub, b));

  assert property (@(posedge clk) disable iff (reset)
    result == (a + inv_b(sub, b)));

  assert property (@(posedge clk) disable iff (reset)
    sum == result && sum == (a + inv_b(sub, b)));

  // Sum is purely combinational of inputs (no unintended state)
  assert property (@(posedge clk) disable iff (reset)
    $stable({a,b,sub}) |-> $stable(sum));

  // No X/Z on outputs when inputs are known
  assert property (@(posedge clk)
    !$isunknown({a,b,sub}) |-> !$isunknown({sum, result, inverted_b}));

  // Carry-lookahead signal correctness (will flag RTL issues)
  assert property (@(posedge clk) disable iff (reset)
    p == (a ^ inv_b(sub, b)));

  assert property (@(posedge clk) disable iff (reset)
    g == (a & inv_b(sub, b)));

  assert property (@(posedge clk) disable iff (reset)
    c == carry_exp(sub, a, b));

  // Storage behavior
  // Synchronous reset value
  assert property (@(posedge clk) reset |=> stored_num == 8'h34);

  // Hold when disabled
  assert property (@(posedge clk) disable iff (reset)
    !enable |=> $stable(stored_num));

  // On falling edge of enable, the value captured in previous cycle must match
  assert property (@(posedge clk) disable iff (reset)
    $fell(enable) |-> stored_num == $past(sum[7:0]));

  // Coverage: exercise add, sub, overflows, zero result, and enable gating
  cover property (@(posedge clk) disable iff (reset) !sub);                          // addition seen
  cover property (@(posedge clk) disable iff (reset)  sub);                          // subtraction seen
  cover property (@(posedge clk) disable iff (reset) !sub && (sum < a));             // unsigned add carry-out
  cover property (@(posedge clk) disable iff (reset)  sub && (a < b));               // unsigned borrow on sub
  cover property (@(posedge clk) disable iff (reset) sum == 32'h0);                  // zero result
  cover property (@(posedge clk) disable iff (reset) $rose(sub));                    // toggle sub
  cover property (@(posedge clk) disable iff (reset) $fell(sub));
  cover property (@(posedge clk) disable iff (reset) $rose(enable));                 // enable on
  cover property (@(posedge clk) disable iff (reset) $fell(enable));                 // enable off
  cover property (@(posedge clk) disable iff (reset)
    $fell(enable) && stored_num == $past(sum[7:0]));                                 // capture event observed

endmodule

// Bind to DUT (connect internal nets for deeper checks)
bind binary_add_sub binary_add_sub_sva sva_inst (
  .clk       (clk),
  .reset     (reset),
  .a         (a),
  .b         (b),
  .sub       (sub),
  .enable    (enable),
  .sum       (sum),
  .result    (result),
  .inverted_b(inverted_b),
  .g         (g),
  .p         (p),
  .c         (c),
  .stored_num(stored_num)
);