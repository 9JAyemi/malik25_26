// SVA for fadder – concise, high-quality checks and coverage
// Bindable checker; no DUT/testbench changes required.

module fadder_sva #(parameter int WIDTH = 8)
(
  input  logic [WIDTH-1:0] a,
  input  logic [WIDTH-1:0] b,
  input  logic             sub_enable,
  input  logic             carry_in,
  input  logic [WIDTH-1:0] res,
  input  logic             carry_out
);

  // Helpers
  let has_x   = $isunknown({a,b,sub_enable,carry_in});
  let b_eff   = sub_enable ? ~b : b;
  let sum_ext = {1'b0,a} + {1'b0,b_eff} + carry_in;

  // Structural/algebraic correctness (primary spec)
  assert property (@(*)) disable iff (has_x)
    {carry_out, res} == sum_ext;

  // Bit-0 behavior (sanity on LSB stage)
  assert property (@(*)) disable iff (has_x)
    res[0] == (a[0] ^ b_eff[0] ^ carry_in);

  // Subtraction-specific carry/borrow semantics
  // a - b when carry_in==1: carry_out==1 iff a>=b
  assert property (@(*)) disable iff (has_x)
    (sub_enable &&  carry_in) |-> (carry_out == (a >= b));

  // a - b - 1 when carry_in==0: carry_out==1 iff a>b
  assert property (@(*)) disable iff (has_x)
    (sub_enable && !carry_in) |-> (carry_out == (a >  b));

  // Useful corner cases
  assert property (@(*)) disable iff (has_x)
    (sub_enable &&  carry_in && (a==b)) |-> (res=='0 && carry_out);

  assert property (@(*)) disable iff (has_x)
    (sub_enable && !carry_in && (a==b)) |-> (res=={WIDTH{1'b1}} && !carry_out);

  assert property (@(*)) disable iff (has_x)
    (!sub_enable && (b=='0) && !carry_in) |-> (res==a && !carry_out);

  // Knownness: if inputs are 2-state, outputs must be 2-state
  assert property (@(*))
    has_x or (!$isunknown({res,carry_out}));

  // Coverage: exercise modes, edges, and long propagate chain
  cover property (@(*)) !has_x && !sub_enable && !carry_in;
  cover property (@(*)) !has_x && !sub_enable &&  carry_in;
  cover property (@(*)) !has_x &&  sub_enable && !carry_in;
  cover property (@(*)) !has_x &&  sub_enable &&  carry_in;

  // Zero result in subtract (equal operands)
  cover property (@(*)) !has_x && sub_enable && carry_in && (a==b) && (res=='0) && carry_out;

  // Full carry-propagation across WIDTH bits
  cover property (@(*)) !has_x && carry_in &&
                        ((a ^ b_eff) == {WIDTH{1'b1}}) && carry_out;

  // Addition overflow case
  cover property (@(*)) !has_x && !sub_enable && carry_in &&
                        (a=={WIDTH{1'b1}}) && (b=={WIDTH{1'b1}}) && carry_out;

endmodule

// Example bind (instantiate once per fadder instance):
// bind fadder fadder_sva #(.WIDTH(WIDTH)) u_fadder_sva (.*);