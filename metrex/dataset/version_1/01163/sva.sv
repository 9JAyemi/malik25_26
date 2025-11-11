// SVA for or4: bindable checker + full functional/coverage checks

checker or4_sva (
  input logic A, B, C, D,
  input logic X,
  input logic AB, CD, ABCD,
  input logic VPWR, VGND, VPB, VNB
);

  // Combinational functional correctness (including internal nets)
  always_comb begin
    assert (AB   === (A | B))        else $error("AB != A|B");
    assert (CD   === (C | D))        else $error("CD != C|D");
    assert (ABCD === (AB | CD))      else $error("ABCD != AB|CD");
    assert (X    === (A | B | C | D)) else $error("X != A|B|C|D");
  end

  // X-propagation sanity: known inputs must yield known output
  always_comb if (!$isunknown({A,B,C,D}))
    assert (!$isunknown(X)) else $error("X unknown with known inputs");

  // Power pins tied correctly
  always_comb
    assert (VPWR===1'b1 && VPB===1'b1 && VGND===1'b0 && VNB===1'b0)
      else $error("Power/Ground pins incorrect");

  // No spurious output toggles without input activity
  assert property ( $changed(X) |-> $changed({A,B,C,D}) );

  // Truth-table coverage: all 16 input minterms with correct X
  genvar i;
  for (i = 0; i < 16; i++) begin : g_minterm_cov
    localparam logic [3:0] P = i[3:0];
    cover property ( {A,B,C,D} === P && X === (|P) );
  end
endchecker

// Bind into the DUT (connects to ports and internal nets by name)
bind or4 or4_sva or4_sva_b (.*);