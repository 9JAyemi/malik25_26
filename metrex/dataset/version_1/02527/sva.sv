// SVA for soft_clock
// Bind this module to the DUT to check key behaviors concisely.

module soft_clock_sva
  #(parameter C_SIPIF_DWIDTH = 32)
(
  input  logic                              Bus2IP_Reset,
  input  logic                              Bus2IP_Clk,
  input  logic                              Bus2IP_WrCE,
  input  logic [0:C_SIPIF_DWIDTH-1]         Bus2IP_Data,
  input  logic [0:(C_SIPIF_DWIDTH/8)-1]     Bus2IP_BE,

  input  logic                              Clk2IP_Clk,
  input  logic                              Clk2Bus_WrAck,
  input  logic                              Clk2Bus_Error,
  input  logic                              Clk2Bus_ToutSup,

  // internal DUT state (bound hierarchically)
  input  logic                              isr_ce,
  input  logic                              isr_error
);

  // local decodes (match DUT)
  localparam logic [0:3] CLOCK_ENABLE  = 4'b1010;
  localparam logic [0:3] CLOCK_DISABLE = 4'b0101;

  let nibble        = Bus2IP_Data[C_SIPIF_DWIDTH-4:C_SIPIF_DWIDTH-1];
  let be_top        = Bus2IP_BE[(C_SIPIF_DWIDTH/8)-1];
  let enable_match  = (nibble == CLOCK_ENABLE);
  let disable_match = (nibble == CLOCK_DISABLE);
  let match         = enable_match || disable_match;
  let mismatch      = !(match);
  let be_match      = (be_top == 1'b1);

  default clocking cb @(posedge Bus2IP_Clk); endclocking
  default disable iff (Bus2IP_Reset);

  // Reset/tout supervision
  assert property (@(posedge Bus2IP_Clk) $rose(Bus2IP_Reset) |=> (isr_ce==1'b1 && isr_error==1'b0));
  assert property (@(posedge Bus2IP_Clk) Clk2Bus_ToutSup == Bus2IP_Reset);

  // Output definitions and exclusivity
  assert property (Clk2Bus_WrAck  == (match    && Bus2IP_WrCE && be_match));
  assert property (Clk2Bus_Error  == (mismatch && Bus2IP_WrCE && be_match));
  assert property (!(Clk2Bus_WrAck && Clk2Bus_Error));
  assert property ((Bus2IP_WrCE && be_match) |-> (Clk2Bus_WrAck ^ Clk2Bus_Error));

  // Gated clock correctness
  assert property (Clk2IP_Clk == (Bus2IP_Clk & isr_ce));
  assert property (!$isunknown({Clk2IP_Clk, Clk2Bus_WrAck, Clk2Bus_Error})) else $error("X/Z on outputs");

  // isr_ce update semantics
  assert property ((Bus2IP_WrCE && be_match && enable_match)  |=> (isr_ce==1'b1));
  assert property ((Bus2IP_WrCE && be_match && disable_match) |=> (isr_ce==1'b0));
  assert property (!(Bus2IP_WrCE && be_match && (enable_match || disable_match)) |=> $stable(isr_ce));

  // isr_error update semantics (independent of BE)
  assert property ( Bus2IP_WrCE |=> (isr_error == mismatch));
  assert property (!Bus2IP_WrCE |=> $stable(isr_error));

  // Coverage
  cover property (Bus2IP_WrCE && be_match && disable_match ##1 (isr_ce==1'b0));
  cover property (Bus2IP_WrCE && be_match && enable_match  ##1 (isr_ce==1'b1));
  cover property (Bus2IP_WrCE && be_match &&  match && Clk2Bus_WrAck);
  cover property (Bus2IP_WrCE && be_match && !match && Clk2Bus_Error);
  cover property (Bus2IP_WrCE && !be_match && !match ##1 (isr_error==1'b1) and !(Clk2Bus_WrAck || Clk2Bus_Error));
  cover property ((Bus2IP_WrCE && be_match && disable_match) ##1 (Bus2IP_WrCE && be_match && enable_match));

endmodule

// Bind into DUT
bind soft_clock soft_clock_sva #(.C_SIPIF_DWIDTH(C_SIPIF_DWIDTH))
  soft_clock_sva_i (.*,
    .isr_ce(isr_ce),
    .isr_error(isr_error)
  );