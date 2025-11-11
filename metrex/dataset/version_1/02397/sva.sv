// SVA checker for add_sub_mux
// Concise, but covers all key functionality and detects X-propagation and unintended dependencies.

module add_sub_mux_sva (
  input  logic [31:0] a,
  input  logic [31:0] b,
  input  logic        sub,
  input  logic [31:0] result,
  input  logic [31:0] adder_out, // internal wire
  input  logic        mux_out    // internal wire
);

  // Helper: inputs known => outputs known (after delta settle)
  assert property (@(a or b or sub)
                   !$isunknown({a,b,sub}) |-> ##0 !$isunknown({adder_out,mux_out,result}))
    else $error("X/Z detected on outputs with known inputs");

  // Internal adder lower half correctness
  assert property (@(a or b) ##0 adder_out[15:0] == a[15:0] + b[15:0])
    else $error("adder_out[15:0] mismatch");

  // Internal adder upper half correctness (delta to allow NB assign settle)
  assert property (@(a or b) ##0 adder_out[31:16] == a[31:16] + b[31:16])
    else $error("adder_out[31:16] mismatch");

  // Mux correctness (delta to allow settle)
  assert property (@(sub or adder_out[0]) ##0 mux_out == (sub ? ~adder_out[0] : adder_out[0]))
    else $error("mux_out mismatch");

  // Result lower matches design and internal
  assert property (@(a or b) ##0 result[15:0] == a[15:0] + b[15:0])
    else $error("result[15:0] mismatch");
  assert property (@(a or b) ##0 result[15:0] == adder_out[15:0])
    else $error("result[15:0] != adder_out[15:0]");

  // Result upper matches internal combination
  assert property (@(adder_out or mux_out) ##0 result[31:16] == adder_out[31:16] + mux_out)
    else $error("result[31:16] != adder_out[31:16] + mux_out");

  // Result upper matches pure functional spec from inputs
  assert property (@(a or b or sub) ##0
    result[31:16] ==
      (a[31:16] + b[31:16]) +
      (sub ? ~((a[15:0] + b[15:0])[0]) : ((a[15:0] + b[15:0])[0])))
    else $error("result[31:16] functional mismatch");

  // Sub must not affect lower 16b
  assert property (@(sub) $stable(a) && $stable(b) |-> ##0 $stable(result[15:0]))
    else $error("result[15:0] changed on sub toggle");

  // mux_out depends only on adder_out[0] and sub
  assert property (@(adder_out) $changed(adder_out[31:1]) && !$changed(adder_out[0]) && $stable(sub)
                   |-> ##0 $stable(mux_out))
    else $error("mux_out changed due to adder_out[31:1]");

  // Basic functional coverage
  cover property (@(a or b or sub) ##0 (sub==0 && ((a[15:0]+b[15:0])[0]==0)));
  cover property (@(a or b or sub) ##0 (sub==0 && ((a[15:0]+b[15:0])[0]==1)));
  cover property (@(a or b or sub) ##0 (sub==1 && ((a[15:0]+b[15:0])[0]==0)));
  cover property (@(a or b or sub) ##0 (sub==1 && ((a[15:0]+b[15:0])[0]==1)));
  cover property (@(sub) $changed(sub));
  cover property (@(a or b) ##0 (a==32'h0000_0000 && b==32'h0000_0000));
  cover property (@(a or b) ##0 (a==32'hFFFF_FFFF && b==32'hFFFF_FFFF));

endmodule

// Bind into DUT (gives checker access to internals)
bind add_sub_mux add_sub_mux_sva sva_add_sub_mux (
  .a(a),
  .b(b),
  .sub(sub),
  .result(result),
  .adder_out(adder_out),
  .mux_out(mux_out)
);