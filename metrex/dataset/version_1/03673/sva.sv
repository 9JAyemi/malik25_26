// SVA for Multiplexer_4to1 and LUT4
`ifndef MUX_LUT4_SVA
`define MUX_LUT4_SVA

// 4:1 MUX SVA
module Multiplexer_4to1_sva(
  input logic       ctrl0, ctrl1,
  input logic [0:0] D0, D1, D2, D3,
  input logic [0:0] S
);
  default clocking cb @(*); endclocking

  // Functional correctness (when all relevant signals are known)
  assert property ( !$isunknown({ctrl1,ctrl0,D0,D1,D2,D3})
                    |-> S == (ctrl1 ? (ctrl0 ? D3 : D2) : (ctrl0 ? D1 : D0)) );

  // Output not X when inputs known
  assert property ( !$isunknown({ctrl1,ctrl0,D0,D1,D2,D3}) |-> !$isunknown(S) );

  // No spurious output changes
  assert property ( $changed(S) |-> $changed({ctrl1,ctrl0,D0,D1,D2,D3}) );

  // Path coverage
  cover property ( {ctrl1,ctrl0}==2'b00 && !$isunknown(D0) && S==D0 );
  cover property ( {ctrl1,ctrl0}==2'b01 && !$isunknown(D1) && S==D1 );
  cover property ( {ctrl1,ctrl0}==2'b10 && !$isunknown(D2) && S==D2 );
  cover property ( {ctrl1,ctrl0}==2'b11 && !$isunknown(D3) && S==D3 );

  // Toggle coverage
  cover property ( $rose(S[0]) );
  cover property ( $fell(S[0]) );
endmodule

bind Multiplexer_4to1 Multiplexer_4to1_sva m4_sva (.*);

// LUT4 SVA
module LUT4_sva(
  input logic [3:0] I,
  input logic       O
);
  default clocking cb @(*); endclocking

  // Inputs known and functional correctness
  assert property ( !$isunknown(I) );
  assert property ( !$isunknown(I) |-> O == (I[0] ~^ I[3]) );

  // Output not X when inputs known
  assert property ( !$isunknown(I) |-> !$isunknown(O) );

  // No spurious output changes
  assert property ( $changed(O) |-> $changed(I) );

  // Full input space coverage and both output polarities
  for (genvar v=0; v<16; v++) begin : c_all_I
    localparam logic [3:0] VAL = v[3:0];
    cover property ( I == VAL );
  end
  cover property ( O==1 );
  cover property ( O==0 );
endmodule

bind LUT4 LUT4_sva lut4_sva (.*);

`endif