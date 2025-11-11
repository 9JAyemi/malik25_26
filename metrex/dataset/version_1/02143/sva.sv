// SVA checker for binary_to_gray
// Sample on any convenient TB clock: connect .clk to your env clock.
module binary_to_gray_sva (
  input logic        clk,
  input logic [2:0]  B,
  input logic [2:0]  G
);
  function automatic logic [2:0] gray3 (input logic [2:0] b);
    return {b[2], b[2]^b[1], b[1]^b[0]};
  endfunction

  default clocking cb @(posedge clk); endclocking

  // Functional equivalence
  ap_func:    assert property (G === gray3(B));

  // No X/Z on output when inputs are known
  ap_known:   assert property (!$isunknown(B) |-> !$isunknown(G));

  // Output stable when input stable (no unintended combinational memory)
  ap_stable:  assert property ($stable(B) |-> $stable(G));

  // Gray adjacency: consecutive binary +/-1 steps change exactly one Gray bit
  ap_adj:     assert property ((B == $past(B)+1 || B == $past(B)-1)
                               |-> $countones(G ^ $past(G)) == 1);

  // Functional coverage: all input codes map to expected Gray code
  genvar i;
  generate
    for (i = 0; i < 8; i++) begin : C_MAP
      c_map: cover property (B == i[2:0] && G == gray3(i[2:0]));
    end
  endgenerate

  // Transition coverage: observe all +/-1 binary steps and 1-bit Gray change
  generate
    for (i = 0; i < 7; i++) begin : C_UP
      c_up: cover property ($past(B) == i[2:0] && B == (i+1)[2:0]
                            && $countones(G ^ $past(G)) == 1);
    end
    for (i = 1; i < 8; i++) begin : C_DN
      c_dn: cover property ($past(B) == i[2:0] && B == (i-1)[2:0]
                            && $countones(G ^ $past(G)) == 1);
    end
  endgenerate
endmodule

// Bind example (connect clk to your TB clock signal)
bind binary_to_gray binary_to_gray_sva u_binary_to_gray_sva (.clk(clk), .B(B), .G(G));