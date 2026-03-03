// SVA checker for DecodeUnitRegisterTwo
module DecodeUnitRegisterTwo_sva (
  input  CLK,
  // DUT inputs
  input  input_IN, wren_IN,
  input  [2:0] writeAd_IN,
  input  ADR_MUX_IN, write_IN, PC_load_IN,
  input  SPR_w_IN, SPR_i_IN, SPR_d_IN,
  input  [2:0] cond_IN, op2_IN,
  input  SW_IN, MAD_MUX_IN,
  // DUT outputs
  input  input_OUT, wren_OUT,
  input  [2:0] writeAd_OUT,
  input  ADR_MUX_OUT, write_OUT, PC_load_OUT,
  input  SPR_w_OUT, SPR_i_OUT, SPR_d_OUT,
  input  [2:0] cond_OUT, op2_OUT,
  input  SW_OUT, MAD_MUX_OUT
);

  default clocking cb @(posedge CLK); endclocking

  // 1-cycle pipeline equivalence (captures input value, checks next cycle output)
  property d1_bool(logic in_s, logic out_s);
    logic v;
    (1, v = in_s) |=> (out_s == v);
  endproperty
  property d1_vec3(logic [2:0] in_s, logic [2:0] out_s);
    logic [2:0] v;
    (1, v = in_s) |=> (out_s == v);
  endproperty

  // Check each signal
  assert property (d1_bool(input_IN , input_OUT ));
  assert property (d1_bool(wren_IN  , wren_OUT  ));
  assert property (d1_vec3(writeAd_IN, writeAd_OUT));
  assert property (d1_bool(ADR_MUX_IN, ADR_MUX_OUT));
  assert property (d1_bool(write_IN , write_OUT ));
  assert property (d1_bool(PC_load_IN, PC_load_OUT));
  assert property (d1_bool(SPR_w_IN , SPR_w_OUT ));
  assert property (d1_bool(SPR_i_IN , SPR_i_OUT ));
  assert property (d1_bool(SPR_d_IN , SPR_d_OUT ));
  assert property (d1_vec3(cond_IN  , cond_OUT  ));
  assert property (d1_vec3(op2_IN   , op2_OUT   ));
  assert property (d1_bool(SW_IN    , SW_OUT    ));
  assert property (d1_bool(MAD_MUX_IN, MAD_MUX_OUT));

  // Outputs must only change on rising CLK (no async glitches)
  assert property ( $changed(input_OUT ) |-> $rose(CLK) );
  assert property ( $changed(wren_OUT  ) |-> $rose(CLK) );
  assert property ( $changed(writeAd_OUT) |-> $rose(CLK) );
  assert property ( $changed(ADR_MUX_OUT) |-> $rose(CLK) );
  assert property ( $changed(write_OUT ) |-> $rose(CLK) );
  assert property ( $changed(PC_load_OUT) |-> $rose(CLK) );
  assert property ( $changed(SPR_w_OUT ) |-> $rose(CLK) );
  assert property ( $changed(SPR_i_OUT ) |-> $rose(CLK) );
  assert property ( $changed(SPR_d_OUT ) |-> $rose(CLK) );
  assert property ( $changed(cond_OUT  ) |-> $rose(CLK) );
  assert property ( $changed(op2_OUT   ) |-> $rose(CLK) );
  assert property ( $changed(SW_OUT    ) |-> $rose(CLK) );
  assert property ( $changed(MAD_MUX_OUT) |-> $rose(CLK) );

  // Lightweight coverage
  // - Each output changes at least once
  cover property ( $changed(input_OUT ) );
  cover property ( $changed(wren_OUT  ) );
  cover property ( $changed(writeAd_OUT) );
  cover property ( $changed(ADR_MUX_OUT) );
  cover property ( $changed(write_OUT ) );
  cover property ( $changed(PC_load_OUT) );
  cover property ( $changed(SPR_w_OUT ) );
  cover property ( $changed(SPR_i_OUT ) );
  cover property ( $changed(SPR_d_OUT ) );
  cover property ( $changed(cond_OUT  ) );
  cover property ( $changed(op2_OUT   ) );
  cover property ( $changed(SW_OUT    ) );
  cover property ( $changed(MAD_MUX_OUT) );

  // - Boolean toggles both directions at least once
  cover property ( !$past(input_OUT) &&  input_OUT );
  cover property (  $past(input_OUT) && !input_OUT );
  cover property ( !$past(wren_OUT ) &&  wren_OUT  );
  cover property (  $past(wren_OUT ) && !wren_OUT  );
  cover property ( !$past(ADR_MUX_OUT) &&  ADR_MUX_OUT );
  cover property (  $past(ADR_MUX_OUT) && !ADR_MUX_OUT );
  cover property ( !$past(write_OUT) &&  write_OUT );
  cover property (  $past(write_OUT) && !write_OUT );
  cover property ( !$past(PC_load_OUT) &&  PC_load_OUT );
  cover property (  $past(PC_load_OUT) && !PC_load_OUT );
  cover property ( !$past(SPR_w_OUT) &&  SPR_w_OUT );
  cover property (  $past(SPR_w_OUT) && !SPR_w_OUT );
  cover property ( !$past(SPR_i_OUT) &&  SPR_i_OUT );
  cover property (  $past(SPR_i_OUT) && !SPR_i_OUT );
  cover property ( !$past(SPR_d_OUT) &&  SPR_d_OUT );
  cover property (  $past(SPR_d_OUT) && !SPR_d_OUT );
  cover property ( !$past(SW_OUT) &&  SW_OUT );
  cover property (  $past(SW_OUT) && !SW_OUT );
  cover property ( !$past(MAD_MUX_OUT) &&  MAD_MUX_OUT );
  cover property (  $past(MAD_MUX_OUT) && !MAD_MUX_OUT );

  // - 3-bit vectors hit extremes
  cover property (writeAd_OUT == 3'h0);
  cover property (writeAd_OUT == 3'h7);
  cover property (cond_OUT    == 3'h0);
  cover property (cond_OUT    == 3'h7);
  cover property (op2_OUT     == 3'h0);
  cover property (op2_OUT     == 3'h7);

endmodule

// Bind example (instantiate with your DUT instance name)
// bind DecodeUnitRegisterTwo DecodeUnitRegisterTwo_sva sva(.*);