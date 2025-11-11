// SVA for lcd_driver
// Bind this module to the DUT
bind lcd_driver lcd_driver_sva i_lcd_driver_sva();

module lcd_driver_sva;

  // Use DUT clock/reset and signals via bind scope
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // ---------------- Assertions ----------------

  // State encoding legal
  a_state_legal: assert property (
    state inside {STATE_IDLE, STATE_WAIT_ENABLE, STATE_SEND_COMMAND, STATE_SEND_DATA}
  );

  // IDLE transitions
  a_idle_to_wait: assert property (
    state==STATE_IDLE && !reset && enable |=> state==STATE_WAIT_ENABLE
  );
  a_idle_hold: assert property (
    state==STATE_IDLE && (reset || !enable) |=> state==STATE_IDLE
  );

  // WAIT_ENABLE transitions
  a_wait_to_idle_reset: assert property (
    state==STATE_WAIT_ENABLE && reset |=> state==STATE_IDLE
  );
  a_wait_to_idle_dis: assert property (
    state==STATE_WAIT_ENABLE && !reset && !enable |=> state==STATE_IDLE
  );
  a_wait_to_cmd: assert property (
    state==STATE_WAIT_ENABLE && !reset && enable && in_cmd |=> state==STATE_SEND_COMMAND
  );
  a_wait_to_data: assert property (
    state==STATE_WAIT_ENABLE && !reset && enable && !in_cmd |=> state==STATE_SEND_DATA
  );

  // SEND_* transitions
  a_send_cmd_to_idle: assert property (state==STATE_SEND_COMMAND |=> state==STATE_IDLE);
  a_send_data_to_idle: assert property (state==STATE_SEND_DATA |=> state==STATE_IDLE);

  // SEND_* can only be reached from WAIT_ENABLE
  a_send_only_from_wait: assert property (
    (state==STATE_SEND_COMMAND || state==STATE_SEND_DATA) |-> $past(state)==STATE_WAIT_ENABLE
  );

  // Output connectivity to internal regs
  a_connect_pins: assert property (
    lcd_pins==lcd_data && rs==lcd_rs && rw==lcd_rw && backlight==lcd_backlight
  );

  // Outputs change only in SEND_* states
  a_outputs_stable_when_not_send: assert property (
    (state==STATE_IDLE || state==STATE_WAIT_ENABLE) |-> $stable({lcd_data,lcd_rs,lcd_rw,lcd_backlight})
  );

  // RW must always be 0 (write-only)
  a_rw_zero: assert property (rw==1'b0);

  // Post-SEND_COMMAND outputs
  a_cmd_outputs: assert property (
    state==STATE_SEND_COMMAND |=> rs==1'b0 && rw==1'b0 && backlight==1'b1 && lcd_pins==$past(in_data)
  );

  // Post-SEND_DATA outputs
  a_data_outputs: assert property (
    state==STATE_SEND_DATA |=> rs==1'b1 && rw==1'b0 && backlight==1'b1 && lcd_pins==$past(in_data)
  );

  // No X on critical registers (outside reset)
  a_no_x_ctrls: assert property (!$isunknown({state,lcd_data,lcd_rs,lcd_rw,lcd_backlight}));

  // Synchronous reset forces IDLE from IDLE/WAIT_ENABLE (not disabled by reset)
  a_reset_forces_idle: assert property (@(posedge clk)
    (state inside {STATE_IDLE,STATE_WAIT_ENABLE} && reset) |=> state==STATE_IDLE
  );

  // ---------------- Coverage ----------------

  c_visit_idle: cover property (state==STATE_IDLE);
  c_visit_wait: cover property (state==STATE_WAIT_ENABLE);
  c_visit_cmd:  cover property (state==STATE_SEND_COMMAND);
  c_visit_data: cover property (state==STATE_SEND_DATA);

  c_idle_to_wait: cover property (state==STATE_IDLE && !reset && enable |=> state==STATE_WAIT_ENABLE);
  c_wait_to_cmd:  cover property (state==STATE_WAIT_ENABLE && !reset && enable && in_cmd |=> state==STATE_SEND_COMMAND);
  c_wait_to_data: cover property (state==STATE_WAIT_ENABLE && !reset && enable && !in_cmd |=> state==STATE_SEND_DATA);
  c_cmd_to_idle:  cover property (state==STATE_SEND_COMMAND |=> state==STATE_IDLE);
  c_data_to_idle: cover property (state==STATE_SEND_DATA |=> state==STATE_IDLE);

  // Cover key command opcodes observed on command path
  c_cmd_clear: cover property (state==STATE_SEND_COMMAND && $past(in_data)==LCD_CLEAR_DISPLAY);
  c_cmd_home:  cover property (state==STATE_SEND_COMMAND && $past(in_data)==LCD_RETURN_HOME);
  c_cmd_entry: cover property (state==STATE_SEND_COMMAND && $past(in_data)==LCD_ENTRY_MODE_SET);
  c_cmd_disp:  cover property (state==STATE_SEND_COMMAND && $past(in_data)==LCD_DISPLAY_ON_OFF_CONTROL);
  c_cmd_shift: cover property (state==STATE_SEND_COMMAND && $past(in_data)==LCD_CURSOR_DISPLAY_SHIFT);
  c_cmd_func:  cover property (state==STATE_SEND_COMMAND && $past(in_data)==LCD_FUNCTION_SET);
  c_cmd_cgram: cover property (state==STATE_SEND_COMMAND && $past(in_data)==LCD_SET_CGRAM_ADDRESS);
  c_cmd_ddram: cover property (state==STATE_SEND_COMMAND && $past(in_data)==LCD_SET_DDRAM_ADDRESS);

endmodule