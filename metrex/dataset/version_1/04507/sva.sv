// SVA checker for OledEX
module OledEX_sva #(
  parameter int unsigned P_EXRESET = 4'h0,
  parameter int unsigned P_EXSEND  = 4'h1,
  parameter int unsigned P_IDLE    = 4'hF
)(
  input  logic        CLK,
  input  logic        RST,
  input  logic        EN,
  input  logic        CS,
  input  logic        SDO,
  input  logic        SCLK,
  input  logic        DC,
  input  logic        FIN,
  input  logic [3:0]  current_state
);

  default clocking cb @(posedge CLK); endclocking

  // No X/Z on critical signals
  a_no_x: assert property (!$isunknown({current_state, CS, SDO, SCLK, DC, FIN})));

  // Constants that never change
  a_const_cs:   assert property (1'b1 |-> CS  === 1'b1);
  a_const_sclk: assert property (1'b1 |-> SCLK=== 1'b0);
  a_const_dc:   assert property (1'b1 |-> DC  === 1'b1);

  // Legal state encoding only
  a_state_legal: assert property (1'b1 |-> current_state inside {P_EXRESET, P_EXSEND, P_IDLE});

  // Reset behavior: next cycle goes to ExampleReset
  a_rst_to_reset: assert property (RST |=> current_state == P_EXRESET);

  // When EN==0 (and not in reset), state and un-driven outputs hold
  a_hold_no_en_state: assert property ((!EN && !RST) |=> $stable(current_state));
  a_hold_no_en_outs:  assert property ((!EN && !RST) |=> $stable({SDO, FIN}));

  // FSM transitions when EN==1
  a_reset_to_send: assert property ((current_state==P_EXRESET && EN && !RST) |=> current_state==P_EXSEND);
  a_send_to_idle:  assert property ((current_state==P_EXSEND  && EN && !RST) |=> current_state==P_IDLE);
  a_idle_sticky:   assert property ((current_state==P_IDLE   && EN && !RST) |=> $stable(current_state));

  // Output effects of states (checked next cycle to avoid NBA race)
  a_sdo_in_reset:  assert property ((current_state==P_EXRESET && EN && !RST) |=> SDO==1'b0);
  a_sdo_in_send:   assert property ((current_state==P_EXSEND  && EN && !RST) |=> SDO==1'b1);
  a_fin_in_idle:   assert property ((current_state==P_IDLE    && EN && !RST) |=> FIN==1'b1);

  // FIN can only rise due to prior Idle with EN
  a_fin_rise_cause: assert property ($rose(FIN) |-> $past(current_state)==P_IDLE && $past(EN)==1'b1 && !$past(RST));

  // Coverage: full path Reset -> Send -> Idle with FIN asserted
  c_full_path: cover property (disable iff (RST)
                               EN && current_state==P_EXRESET
                           ##1 EN && current_state==P_EXSEND
                           ##1 EN && current_state==P_IDLE
                           ##1 FIN);

endmodule

// Bind the checker to the DUT
bind OledEX OledEX_sva #(
  .P_EXRESET(ExampleReset),
  .P_EXSEND (ExampleSendData),
  .P_IDLE   (ExampleIdle)
) OledEX_sva_i (
  .CLK(CLK),
  .RST(RST),
  .EN(EN),
  .CS(CS),
  .SDO(SDO),
  .SCLK(SCLK),
  .DC(DC),
  .FIN(FIN),
  .current_state(current_state)
);