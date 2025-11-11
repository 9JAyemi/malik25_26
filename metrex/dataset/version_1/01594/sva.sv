// SVA checker for shiftll. Bind and drive clk/rst_n from your env.
// Example: bind shiftll shiftll_sva u_shiftll_sva(.clk(tb_clk), .rst_n(tb_rst_n), .*);

module shiftll_sva
(
  input  logic        clk,
  input  logic        rst_n,
  input  logic [31:0] busA,
  input  logic [31:0] sel,
  input  logic [31:0] busSLL,
  input  logic        zSLL,
  input  logic        oSLL,
  input  logic        cSLL,
  input  logic        nSLL
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Functional correctness
  assert property (1'b1 |-> (busSLL == (busA << sel[2:0])));
  assert property (1'b1 |-> (zSLL  == ~|busSLL));
  assert property (1'b1 |-> (nSLL  == busSLL[31]));

  // Carry/Overflow per sel[2:0]
  assert property (1'b1 |-> (
      (sel[2:0]==3'd0) ? (cSLL==1'b0 && oSLL==1'b0) :
      (cSLL == busSLL[32 - sel[2:0]]) &&
      (oSLL == (|busSLL[31 -: sel[2:0]]))
  ));

  // Outputs ignore upper sel bits (combinational dependence only on sel[2:0])
  assert property (($stable(busA) && $stable(sel[2:0]) && $changed(sel[31:3])) |-> $stable({busSLL,zSLL,oSLL,cSLL,nSLL}));

  // Pure combinational behavior (no latches)
  assert property (($stable({busA,sel[2:0]})) |-> $stable({busSLL,zSLL,oSLL,cSLL,nSLL}));

  // No X/Z on outputs when inputs are known
  assert property ((!$isunknown({busA,sel[2:0]})) |-> (!$isunknown({busSLL,zSLL,oSLL,cSLL,nSLL})));

  // Minimal, meaningful coverage
  genvar s;
  generate
    for (s=0; s<8; s++) begin : g_cov_sel
      cover property (sel[2:0]==s[2:0]);
    end
  endgenerate
  cover property (zSLL);
  cover property (!zSLL);
  cover property (nSLL);
  cover property (!nSLL);
  cover property ((sel[2:0]!=3'd0) && oSLL);
  cover property ((sel[2:0]!=3'd0) && cSLL);
  cover property ((sel[2:0]!=3'd0) && oSLL && cSLL);

endmodule