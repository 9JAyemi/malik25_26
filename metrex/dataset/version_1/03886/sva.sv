// SVA for lcd_driver. Bind to all instances of lcd_driver.
module lcd_driver_sva (
  input clk,
  input rst,
  input [7:0] data,
  input rs,
  input rw,
  input en,
  input busy,
  input [3:0] lcd_state,
  input [7:0] lcd_data,
  input [7:0] lcd_instruction,
  input [3:0] lcd_row,
  input [3:0] lcd_col
);

  // Mirror DUT params for readability
  localparam LCD_CLEAR_DISPLAY     = 8'h01;
  localparam LCD_RETURN_HOME       = 8'h02;
  localparam LCD_ENTRY_MODE_SET    = 8'h04;
  localparam LCD_DISPLAY_CONTROL   = 8'h08;
  localparam LCD_CURSOR_SHIFT      = 8'h10;
  localparam LCD_FUNCTION_SET      = 8'h20;
  localparam LCD_SET_CGRAM_ADDR    = 8'h40;
  localparam LCD_SET_DDRAM_ADDR    = 8'h80;

  localparam LCD_FUNCTION_SET_8BIT = 8'h30;
  localparam LCD_FUNCTION_SET_4BIT = 8'h20;
  localparam LCD_DISPLAY_CONTROL_ON= 8'h0C;
  localparam LCD_ENTRY_MODE_SET_INC= 8'h06;

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst)

  // Helper expression for expected DDRAM addr (rows 0/1 only)
  function automatic [7:0] ddram_addr8(input [3:0] r, input [3:0] c);
    ddram_addr8 = LCD_SET_DDRAM_ADDR | ((r[0] ? 8'd64 : 8'd0) + c);
  endfunction

  // Basic sanity/range checks
  a_state_range:      assert property (lcd_state inside {[0:12]});
  a_row_range:        assert property (lcd_row inside {[0:1]});
  a_col_range:        assert property (lcd_col inside {[0:15]});
  a_busy_only_falls:  assert property ($fell(busy) |-> $past(lcd_state) inside {8,12});
  a_busy_only_rises:  assert property ($rose(busy) |-> $past(lcd_state) inside {0,9,11});

  // Initialization sequence and busy behavior
  a_init_progress: assert property (
    lcd_state==0 |=> (lcd_state==1 && busy && lcd_instruction==LCD_FUNCTION_SET_8BIT)
                 ##1 (lcd_state==2 && lcd_instruction==LCD_FUNCTION_SET_8BIT)
                 ##1 (lcd_state==3 && lcd_instruction==LCD_FUNCTION_SET_8BIT)
                 ##1 (lcd_state==4 && lcd_instruction==LCD_FUNCTION_SET_4BIT)
                 ##1 (lcd_state==5 && lcd_instruction==LCD_DISPLAY_CONTROL_ON)
                 ##1 (lcd_state==6 && lcd_instruction==LCD_ENTRY_MODE_SET_INC)
                 ##1 (lcd_state==7 && lcd_instruction==LCD_CLEAR_DISPLAY)
                 ##1 (lcd_state==8 && busy==0)
                 ##1 (lcd_state==9)
  );
  a_busy_during_init: assert property ((lcd_state inside {[1:7]}) |-> busy);

  // Idle state characteristics
  a_idle_not_busy:    assert property (lcd_state==9 |-> !busy);

  // Accept in state 9 only; next state and busy set
  a_accept_to_10: assert property (
    (lcd_state==9 && en && !busy) |=> (lcd_state==10 && busy)
  );

  // Command/data load at accept
  a_accept_data_path: assert property (
    (lcd_state==9 && en && !busy && rs) |=> (lcd_instruction == ddram_addr8($past(lcd_row), $past(lcd_col)) &&
                                             lcd_data        == $past(data))
  );
  a_accept_instr_path: assert property (
    (lcd_state==9 && en && !busy && !rs) |=> (lcd_instruction == $past(data))
  );

  // Handshake phases: set E bit in state10, clear it in state12; enforce progress when en follows the handshake
  a_10_en_sets_e: assert property (lcd_state==10 && en |=> (lcd_state==11 && lcd_instruction[0]==1'b1));
  a_11_negedge_en_to_12: assert property (lcd_state==11 && !en |=> (lcd_state==12 && busy)); // busy held
  a_12_en_clears_e_and_done: assert property (
    lcd_state==12 && en |=> (lcd_state==9 && !busy && lcd_instruction[0]==1'b0)
  );

  // Data clear on completion for RS=1 path
  a_data_cleared_on_done: assert property (
    $past(lcd_state==12 && en && rs) |=> (lcd_data==8'h00)
  );

  // Row/col update on completion
  a_col_inc: assert property (
    (lcd_state==12 && en && $past(lcd_col)!=4'd15) |=> (lcd_col==$past(lcd_col)+1 && lcd_row==$past(lcd_row))
  );
  a_col_wrap_row_toggle: assert property (
    (lcd_state==12 && en && $past(lcd_col)==4'd15) |=> (lcd_col==0 && lcd_row==$past(lcd_row)^1'b1)
  );

  // Keep RS stable across a transaction (environmental assumption for correctness)
  as_rs_stable: assume property (
    (lcd_state==9 && en && !busy) |-> $stable(rs) until_with (lcd_state==9 && !busy)
  );
  // Optional: reads not supported; assume write-only
  as_rw_write_only: assume property (rw==1'b0);

  // Coverage
  c_init:         cover property (lcd_state==0 ##1 lcd_state==9 && !busy);
  c_write_data:   cover property (
                    (lcd_state==9 && en && !busy && rs)
                 ##1 (lcd_state==10 && en)
                 ##1 (lcd_state==11 && !en)
                 ##1 (lcd_state==12 && en)
                 ##1 (lcd_state==9 && !busy)
                  );
  c_write_instr:  cover property (
                    (lcd_state==9 && en && !busy && !rs)
                 ##1 (lcd_state==10 && en)
                 ##1 (lcd_state==11 && !en)
                 ##1 (lcd_state==12 && en)
                 ##1 (lcd_state==9 && !busy)
                  );
  c_wrap:         cover property (
                    (lcd_state==9 && en && !busy && rs && lcd_col==4'd15)
                 ##1 (lcd_state==10 && en)
                 ##1 (lcd_state==11 && !en)
                 ##1 (lcd_state==12 && en)
                 ##1 (lcd_state==9 && !busy && lcd_col==4'd0)
                  );

endmodule

bind lcd_driver lcd_driver_sva i_lcd_driver_sva(.*);