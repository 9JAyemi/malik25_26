// SVA for zybo_top
module zybo_top_sva (
  input  logic         CLK_125MHZ_I,
  input  logic  [3:0]  BUTTONS_I,
  input  logic  [3:0]  SWITCHES_I,
  input  logic  [3:0]  LEDS_O,
  input  logic         PMOD_E_2_TXD_O,
  input  logic         PMOD_E_3_RXD_I,
  input  logic [31:0]  bogoinput,
  input  logic [31:0]  dbg_out,
  input  logic [31:0]  dbg_in,
  input  logic         reset
);

  default clocking cb @(posedge CLK_125MHZ_I); endclocking

  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge CLK_125MHZ_I) past_valid <= 1'b1;

  // Combinational intents
  assert property (reset == (|BUTTONS_I));
  assert property (LEDS_O == (dbg_out[31:28]^dbg_out[27:24]^dbg_out[23:20]^dbg_out[19:16]^dbg_out[15:12]^dbg_out[11: 8]^dbg_out[ 7: 4]^dbg_out[ 3: 0]));
  assert property (PMOD_E_2_TXD_O == PMOD_E_3_RXD_I);
  always @* assert (PMOD_E_2_TXD_O === PMOD_E_3_RXD_I);

  // Synchronous reset behavior
  assert property (reset |-> (bogoinput==32'h0 && dbg_out==32'h0 && dbg_in==32'h0));

  // Next-state relations when not in reset
  assert property (past_valid && !reset |-> bogoinput == { $past(SWITCHES_I), 24'h0 });
  assert property (past_valid && !reset |-> (dbg_in == dbg_out && dbg_out == $past(dbg_out + bogoinput)));

  // Sanity: no X/Z after first clock
  assert property (past_valid |-> !$isunknown({LEDS_O, PMOD_E_2_TXD_O, dbg_out, dbg_in, bogoinput, reset}));

  // Coverage
  cover property ($rose(reset));
  cover property ($fell(reset));
  cover property (past_valid && !reset && $changed(SWITCHES_I));
  cover property ($changed(LEDS_O));
  cover property ($changed(PMOD_E_3_RXD_I));

endmodule

bind zybo_top zybo_top_sva sva_i (.*);