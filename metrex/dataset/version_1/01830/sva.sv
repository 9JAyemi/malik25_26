// SVA for serial_interface
module serial_interface_sva (
  input         clk,
  input         reset,
  input  [3:0]  mcu_data,
  input         mcu_data_valid,
  input  [3:0]  periph_data,
  input         periph_data_valid,
  input         mcu_data_ready,
  input         periph_data_ready,
  input  [3:0]  mcu_response,
  input  [3:0]  periph_response,
  input  [1:0]  state_reg,
  input  [3:0]  mcu_buffer,
  input  [3:0]  periph_buffer
);

  default clocking cb @ (posedge clk); endclocking
  default disable iff (reset);

  // Reset behavior (checked one cycle after reset high)
  assert property (@(posedge clk) disable iff (1'b0)
    reset |=> (state_reg==2'b00 &&
               mcu_buffer==4'h0 && periph_buffer==4'h0 &&
               mcu_data_ready==1'b0 && periph_data_ready==1'b0 &&
               mcu_response==4'h0 && periph_response==4'h0));

  // State legality
  assert property (state_reg inside {2'b00,2'b01,2'b10});

  // Ready flags are mutually exclusive
  assert property (!(mcu_data_ready && periph_data_ready));

  // Start of MCU->PERIPH transfer from IDLE
  assert property (
    (state_reg==2'b00 && mcu_data_valid && !periph_data_ready)
      |=> (state_reg==2'b01 && mcu_data_ready && mcu_buffer==$past(mcu_data))
  );

  // Start of PERIPH->MCU transfer from IDLE
  assert property (
    (state_reg==2'b00 && !mcu_data_ready && periph_data_valid)
      |=> (state_reg==2'b10 && periph_data_ready && periph_buffer==$past(periph_data))
  );

  // Completion of MCU->PERIPH (response update, clear flags, back to IDLE)
  assert property (
    (state_reg==2'b01 && periph_data_ready)
      |=> (state_reg==2'b00 && !mcu_data_ready && !periph_data_ready &&
           periph_response==$past(mcu_buffer))
  );

  // Completion of PERIPH->MCU (response update, clear flags, back to IDLE)
  assert property (
    (state_reg==2'b10 && mcu_data_ready)
      |=> (state_reg==2'b00 && !mcu_data_ready && !periph_data_ready &&
           mcu_response==$past(periph_buffer))
  );

  // Liveness: a started transfer eventually completes and returns to IDLE
  assert property (
    (state_reg==2'b00 && mcu_data_valid && !periph_data_ready)
      |-> ##[1:$] (state_reg==2'b01 && periph_data_ready) ##1 (state_reg==2'b00)
  );
  assert property (
    (state_reg==2'b00 && !mcu_data_ready && periph_data_valid)
      |-> ##[1:$] (state_reg==2'b10 && mcu_data_ready) ##1 (state_reg==2'b00)
  );

  // Buffers stable while waiting
  assert property (state_reg==2'b01 |-> $stable(mcu_buffer));
  assert property (state_reg==2'b10 |-> $stable(periph_buffer));

  // Responses change only on corresponding completion
  assert property ($changed(periph_response) |-> $past(state_reg==2'b01 && periph_data_ready));
  assert property ($changed(mcu_response)    |-> $past(state_reg==2'b10 && mcu_data_ready));

  // No X/Z on key control/outputs
  assert property (!$isunknown({state_reg, mcu_data_ready, periph_data_ready, mcu_response, periph_response}));

  // Coverage: both directions complete
  cover property (
    (state_reg==2'b00 && mcu_data_valid && !periph_data_ready)
      ##1 (state_reg==2'b01 && mcu_data_ready)
      ##[1:$] (state_reg==2'b01 && periph_data_ready)
      ##1 (state_reg==2'b00 && periph_response==$past(mcu_buffer))
  );
  cover property (
    (state_reg==2'b00 && !mcu_data_ready && periph_data_valid)
      ##1 (state_reg==2'b10 && periph_data_ready)
      ##[1:$] (state_reg==2'b10 && mcu_data_ready)
      ##1 (state_reg==2'b00 && mcu_response==$past(periph_buffer))
  );

endmodule

// Bind into DUT (connects to internal regs)
bind serial_interface serial_interface_sva sva_serial_interface (
  .clk               (clk),
  .reset             (reset),
  .mcu_data          (mcu_data),
  .mcu_data_valid    (mcu_data_valid),
  .periph_data       (periph_data),
  .periph_data_valid (periph_data_valid),
  .mcu_data_ready    (mcu_data_ready),
  .periph_data_ready (periph_data_ready),
  .mcu_response      (mcu_response),
  .periph_response   (periph_response),
  .state_reg         (state_reg),
  .mcu_buffer        (mcu_buffer),
  .periph_buffer     (periph_buffer)
);