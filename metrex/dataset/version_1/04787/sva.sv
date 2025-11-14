// SVA for top_module (bind in to access internals)
bind top_module top_module_sva sva();

module top_module_sva;

  // Combinational functional correctness (4-state aware)
  always_comb begin
    assert (out_or  === (|in)) else $error("out_or != |in");
    assert (out_xor === (^in)) else $error("out_xor != ^in");
    assert (out_and === (&in)) else $error("out_and != &in"); // flags current RTL bug

    // Internal wire shape checks (width-extension semantics)
    assert (and_wire[0] === (&in) && and_wire[3:1] === 3'b000) else $error("and_wire shape mismatch");
    assert (or_wire[0]  === (|in) && or_wire[3:1]  === 3'b000) else $error("or_wire shape mismatch");
    assert (xor_wire[0] === (^in) && xor_wire[3:1] === 3'b000) else $error("xor_wire shape mismatch");

    // No X on outputs when inputs are known
    if (!$isunknown(in)) assert (!$isunknown({out_and,out_or,out_xor})) else $error("Outputs contain X/Z with known inputs");
  end

  // Concise functional coverage
  always_comb begin
    // Corner patterns
    cover (in == 4'b0000 && out_or==0 && out_xor==0 && out_and==0);
    cover (in == 4'b1111 && out_or==1 && out_xor==0 && out_and==1); // will not hit with current RTL
    // Key behaviors
    cover (|in);   // any bit set
    cover (^in);   // odd parity
    cover (&in);   // all ones (should imply out_and==1 in correct RTL)
  end

endmodule