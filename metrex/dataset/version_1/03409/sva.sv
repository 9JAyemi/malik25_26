// SVA checker for decoder_3to4
module decoder_3to4_sva (
  input logic a, b, c,
  input logic w, x, y, z
);

  // Functional equivalence and structural constraints (combinational)
  always_comb begin
    // Exact combinational function (4-state)
    assert ( {w,x,y,z} === {~(a&b&c), ~(a&b&~c), ~(a&~b&c), ~(a&~b&~c)} )
      else $error("decoder_3to4: output function mismatch");

    // No X/Z on outputs when inputs are known
    if (!$isunknown({a,b,c}))
      assert (!$isunknown({w,x,y,z}))
        else $error("decoder_3to4: X/Z on outputs with known inputs");

    // Active-low one-hot behavior: at most one low always
    assert ($countones(~{w,x,y,z}) <= 1)
      else $error("decoder_3to4: more than one output low");

    // When a==0, all outputs must be 1; when a==1, exactly one low
    if (!a)
      assert (w & x & y & z)
        else $error("decoder_3to4: a==0 requires all outputs high");
    else
      assert ($onehot(~{w,x,y,z}))
        else $error("decoder_3to4: a==1 requires exactly one output low");
  end

  // Coverage (sample after input edges; use ##0 to observe settled values)
  default clocking cb @(posedge a or negedge a or posedge b or negedge b or posedge c or negedge c); endclocking

  // Key functional cases
  cover property (##0 (!a && w && x && y && z));      // a==0 -> all high
  cover property (##0 (a && b && c && !w));           // w low case
  cover property (##0 (a && b && !c && !x));          // x low case
  cover property (##0 (a && !b && c && !y));          // y low case
  cover property (##0 (a && !b && !c && !z));         // z low case

endmodule

// Bind into DUT
bind decoder_3to4 decoder_3to4_sva sva_inst (.*);