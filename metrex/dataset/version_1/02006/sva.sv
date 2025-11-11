// SVA for module address. Bind this file to the DUT.
// Focus: equivalence of all combinational outputs, X-propagation guard, and key functional coverage.

module address_sva (
  input logic               CLK,
  input logic [15:0]        featurebits,
  input logic [23:0]        SNES_ADDR,
  input logic [7:0]         SNES_PA,
  input logic               SNES_ROMSEL,

  input logic [23:0]        ROM_ADDR,
  input logic               ROM_HIT,
  input logic               IS_SAVERAM,
  input logic               IS_ROM,
  input logic               IS_WRITABLE,
  input logic               msu_enable,
  input logic               sgb_enable,
  input logic               r213f_enable,
  input logic               r2100_hit,
  input logic               snescmd_enable,
  input logic               button_enable,
  input logic               button_addr
);

  default clocking cb @(posedge CLK); endclocking

  // Ignore cycles with unknown inputs to avoid false fires on X/Z
  logic has_x;
  assign has_x = $isunknown({featurebits, SNES_ADDR, SNES_PA, SNES_ROMSEL});
  default disable iff (has_x);

  // Output must not be X when inputs are known
  assert property ( !$isunknown({ROM_ADDR, ROM_HIT, IS_SAVERAM, IS_ROM, IS_WRITABLE,
                                 msu_enable, sgb_enable, r213f_enable, r2100_hit,
                                 snescmd_enable, button_enable, button_addr}) );

  // Core decodes and mappings
  assert property ( IS_ROM       == ~SNES_ROMSEL );
  assert property ( IS_SAVERAM   == 1'b0 );
  assert property ( IS_WRITABLE  == IS_SAVERAM );
  assert property ( ROM_HIT      == (~SNES_ROMSEL | IS_SAVERAM) );

  assert property ( ROM_ADDR == {5'h00, SNES_ADDR[19:16], SNES_ADDR[14:0]} );

  // Feature decodes
  assert property ( msu_enable    == (featurebits[3] & (!SNES_ADDR[22] && ((SNES_ADDR[15:0] & 16'hfff8) == 16'h2000))) );

  assert property ( sgb_enable    == ( !SNES_ADDR[22] &&
                                      ( ((SNES_ADDR[15:0] & 16'hf808) == 16'h6000) ||
                                        ((SNES_ADDR[15:0] & 16'hf80F) == 16'h600F) ||
                                        ((SNES_ADDR[15:0] & 16'hf000) == 16'h7000) ) ) );

  assert property ( r213f_enable  == (featurebits[4] & (SNES_PA == 8'h3f)) );
  assert property ( r2100_hit     == (SNES_PA == 8'h00) );

  assert property ( snescmd_enable == ({SNES_ADDR[22], SNES_ADDR[15:9]} == 8'b0_0010101) );

  // Button interface
  assert property ( button_enable == ((({SNES_ADDR[23:2], 2'b00} == 24'h010F10)) &&
                                      (SNES_ADDR[1] != SNES_ADDR[0])) );
  assert property ( button_addr   == ~SNES_ADDR[0] );

  // Functional coverage (hit all key decodes and both states where relevant)
  cover property ( IS_ROM );
  cover property ( !IS_ROM );
  cover property ( ROM_HIT );
  cover property ( !ROM_HIT );

  cover property ( msu_enable );
  cover property ( r213f_enable );
  cover property ( r2100_hit );
  cover property ( snescmd_enable );
  cover property ( button_enable );
  cover property ( button_addr == 1 );
  cover property ( button_addr == 0 );

  // Cover each SGB sub-decode pattern individually (and that they assert sgb_enable)
  cover property ( !SNES_ADDR[22] && ((SNES_ADDR[15:0] & 16'hf808) == 16'h6000) && sgb_enable );
  cover property ( !SNES_ADDR[22] && ((SNES_ADDR[15:0] & 16'hf80F) == 16'h600F) && sgb_enable );
  cover property ( !SNES_ADDR[22] && ((SNES_ADDR[15:0] & 16'hf000) == 16'h7000) && sgb_enable );

endmodule

bind address address_sva sva_inst (.*);