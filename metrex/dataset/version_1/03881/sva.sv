// SVA bind module for top_module: checks functionality, connectivity, and basic coverage
module top_module_sva (
  input  [3:0] in,
  input        out_and,
  input        out_or,
  input        out_xor,
  input  [3:0] and_out,
  input  [3:0] or_out,
  input  [3:0] xor_out
);
  // Combinational, evaluated on any change
  always_comb begin
    // Submodule functional equivalence given connections in1=in2=in
    assert (and_out === (in & in)) else $error("and_out != in & in");
    assert (or_out  === (in | in)) else $error("or_out  != in | in");
    assert (xor_out === (in ^ in)) else $error("xor_out != in ^ in"); // expected 4'b0000

    // Reduction outputs computed correctly from submodule outputs
    assert (out_and === &and_out) else $error("out_and != &and_out");
    assert (out_or  === |or_out ) else $error("out_or  != |or_out");
    assert (out_xor === ^xor_out) else $error("out_xor != ^xor_out");

    // End-to-end behavior
    assert (out_and === &in) else $error("out_and != &in");
    assert (out_or  === |in) else $error("out_or  != |in");
    assert (out_xor === 1'b0) else $error("out_xor != 0");

    // X-propagation sanity: if inputs are 2-state, all outputs must be 2-state
    if (!$isunknown(in))
      assert (!$isunknown({and_out,or_out,xor_out,out_and,out_or,out_xor}))
        else $error("X/Z on outputs with 2-state input");

    // Minimal but meaningful coverage
    cover (in == '0);                                       // all zeros
    cover (in == '1);                                       // all ones
    cover (in inside {4'b0001,4'b0010,4'b0100,4'b1000});    // single-hot
    cover (out_and == 1'b1);                                // reduction AND hit
    cover (out_or  == 1'b0);                                // reduction OR cleared
    cover (out_xor == 1'b0);                                // expected constant
  end
endmodule

bind top_module top_module_sva top_module_sva_i (
  .in(in),
  .out_and(out_and),
  .out_or(out_or),
  .out_xor(out_xor),
  .and_out(and_out),
  .or_out(or_out),
  .xor_out(xor_out)
);