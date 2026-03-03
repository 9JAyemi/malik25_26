// SVA for sky130_fd_sc_lp__nor4bb
// Function: Y = (~A & ~B & C_N & D_N)

module sky130_fd_sc_lp__nor4bb_sva
(
  input logic A,
  input logic B,
  input logic C_N,
  input logic D_N,
  input logic Y
);

  // Combinational functional checks and corner cases
  always_comb begin
    // Full 4-state functional equivalence
    assert (Y === ((~A) & (~B) & C_N & D_N))
      else $error("nor4bb func mismatch: Y=%b A=%b B=%b C_N=%b D_N=%b", Y,A,B,C_N,D_N);

    // Deterministic zeros (controlling values)
    if (A   === 1'b1) assert (Y === 1'b0) else $error("A=1 must force Y=0");
    if (B   === 1'b1) assert (Y === 1'b0) else $error("B=1 must force Y=0");
    if (C_N === 1'b0) assert (Y === 1'b0) else $error("C_N=0 must force Y=0");
    if (D_N === 1'b0) assert (Y === 1'b0) else $error("D_N=0 must force Y=0");

    // Enable polarity sanity
    if ((C_N === 1'b1) && (D_N === 1'b1))
      assert (Y === ((~A) & (~B))) else $error("Enable=1,1: Y must be NOR(A,B)");
    if ((C_N === 1'b0) || (D_N === 1'b0))
      assert (Y === 1'b0) else $error("Enable low must gate Y to 0");

    // No unknowns on Y when inputs are known
    if (!$isunknown({A,B,C_N,D_N}))
      assert (Y === 1'b0 || Y === 1'b1) else $error("Known inputs produced X/Z on Y");

    // Output is never Z
    assert (Y !== 1'bz) else $error("Y is high-Z");
    
    // Hit the single 1-minterm
    cover (A===1'b0 && B===1'b0 && C_N===1'b1 && D_N===1'b1 && Y===1'b1);
  end

  // Functional coverage: hit all 16 known input combinations
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : g_cov
      localparam logic [3:0] v = i[3:0];
      always_comb cover ({A,B,C_N,D_N} === v);
    end
  endgenerate

endmodule

bind sky130_fd_sc_lp__nor4bb sky130_fd_sc_lp__nor4bb_sva sva_inst (.*);