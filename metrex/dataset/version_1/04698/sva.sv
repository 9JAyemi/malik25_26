// SVA checker for DecodeUnitRegisterTwo
module DecodeUnitRegisterTwo_sva (
  input logic CLK,
  input logic input_IN, wren_IN,
  input logic [2:0] writeAd_IN,
  input logic ADR_MUX_IN, write_IN, PC_load_IN,
  input logic SPR_w_IN, SPR_i_IN, SPR_d_IN,
  input logic [2:0] cond_IN, op2_IN,
  input logic SW_IN, MAD_MUX_IN,
  input logic input_OUT, wren_OUT,
  input logic [2:0] writeAd_OUT,
  input logic ADR_MUX_OUT, write_OUT, PC_load_OUT,
  input logic SPR_w_OUT, SPR_i_OUT, SPR_d_OUT,
  input logic [2:0] cond_OUT, op2_OUT,
  input logic SW_OUT, MAD_MUX_OUT
);

  default clocking cb @(posedge CLK); endclocking

  bit started;
  initial started = 0;
  always @(posedge CLK) started <= 1'b1;

  // Convenience vectors
  wire [18:0] OUT_VEC = {input_OUT, wren_OUT, writeAd_OUT, ADR_MUX_OUT, write_OUT, PC_load_OUT,
                         SPR_w_OUT, SPR_i_OUT, SPR_d_OUT, cond_OUT, op2_OUT, SW_OUT, MAD_MUX_OUT};
  wire [18:0] IN_VEC  = {input_IN,  wren_IN,  writeAd_IN,  ADR_MUX_IN,  write_IN,  PC_load_IN,
                         SPR_w_IN,  SPR_i_IN,  SPR_d_IN,  cond_IN,  op2_IN,  SW_IN,  MAD_MUX_IN};

  // Macros
`define A1C(OUT, IN) \
  assert property (disable iff (!started) (!$isunknown($past(IN))) |-> (OUT == $past(IN)));

`define C_TOG(IN, OUT) \
  cover property (disable iff (!started) $rose(IN) ##1 (OUT == $past(IN))); \
  cover property (disable iff (!started) $fell(IN) ##1 (OUT == $past(IN)));

`define C_BUS(IN, OUT) \
  cover property (disable iff (!started) $changed(IN) ##1 (OUT == $past(IN)));

  // One-cycle latency: per-signal (better debug granularity)
  `A1C(input_OUT,  input_IN)
  `A1C(wren_OUT,   wren_IN)
  `A1C(writeAd_OUT,writeAd_IN)
  `A1C(ADR_MUX_OUT,ADR_MUX_IN)
  `A1C(write_OUT,  write_IN)
  `A1C(PC_load_OUT,PC_load_IN)
  `A1C(SPR_w_OUT,  SPR_w_IN)
  `A1C(SPR_i_OUT,  SPR_i_IN)
  `A1C(SPR_d_OUT,  SPR_d_IN)
  `A1C(cond_OUT,   cond_IN)
  `A1C(op2_OUT,    op2_IN)
  `A1C(SW_OUT,     SW_IN)
  `A1C(MAD_MUX_OUT,MAD_MUX_IN)

  // Aggregate no-glitch: outputs stable between clock edges
  assert property (@(negedge CLK) disable iff (!started)
                   $stable(OUT_VEC) until_with posedge CLK);

  // Aggregate functional check (redundant with per-signal but concise)
  assert property (disable iff (!started)
                   (!$isunknown($past(IN_VEC))) |-> (OUT_VEC == $past(IN_VEC)));

  // Coverage: propagation of toggles/changes
  `C_TOG(input_IN,   input_OUT)
  `C_TOG(wren_IN,    wren_OUT)
  `C_TOG(ADR_MUX_IN, ADR_MUX_OUT)
  `C_TOG(write_IN,   write_OUT)
  `C_TOG(PC_load_IN, PC_load_OUT)
  `C_TOG(SPR_w_IN,   SPR_w_OUT)
  `C_TOG(SPR_i_IN,   SPR_i_OUT)
  `C_TOG(SPR_d_IN,   SPR_d_OUT)
  `C_TOG(SW_IN,      SW_OUT)
  `C_TOG(MAD_MUX_IN, MAD_MUX_OUT)
  `C_BUS(writeAd_IN, writeAd_OUT)
  `C_BUS(cond_IN,    cond_OUT)
  `C_BUS(op2_IN,     op2_OUT)

endmodule

// Bind to all instances of the DUT
bind DecodeUnitRegisterTwo DecodeUnitRegisterTwo_sva sva_i (.*);