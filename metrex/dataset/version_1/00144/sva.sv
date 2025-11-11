// SVA for lcd_driver
// Bind this module to the DUT to check/cover behavior
module lcd_driver_sva #(
  parameter int n = 8,
  parameter int m = 16
) (
  input  logic                clk,
  input  logic                rst,
  input  logic [n-1:0]        data,
  input  logic [m-1:0]        out,
  input  logic [3:0]          lcd_state,
  input  logic [3:0]          lcd_row,
  input  logic [3:0]          lcd_col,
  input  logic [3:0]          cmd_bus,
  input  logic [3:0]          data_bus
);

  // Mirror DUT params (must match DUT)
  localparam logic [7:0] ASCII_A = 8'h41;
  localparam logic [7:0] ASCII_0 = 8'h30;

  localparam logic [3:0] CMD_CLEAR_DISPLAY         = 4'b0001;
  localparam logic [3:0] CMD_RETURN_HOME           = 4'b0010;
  localparam logic [3:0] CMD_ENTRY_MODE_SET        = 4'b0110;
  localparam logic [3:0] CMD_DISPLAY_ON_OFF_CONTROL= 4'b1000;
  localparam logic [3:0] CMD_FUNCTION_SET          = 4'b0010;

  localparam logic [3:0] STATE_INIT                     = 4'b0000;
  localparam logic [3:0] STATE_CLEAR_DISPLAY            = 4'b0001;
  localparam logic [3:0] STATE_RETURN_HOME              = 4'b0010;
  localparam logic [3:0] STATE_ENTRY_MODE_SET           = 4'b0011;
  localparam logic [3:0] STATE_DISPLAY_ON_OFF_CONTROL   = 4'b0100;
  localparam logic [3:0] STATE_FUNCTION_SET             = 4'b0101;
  localparam logic [3:0] STATE_WRITE_DATA               = 4'b0110;
  localparam logic [3:0] STATE_WRITE_COMMAND            = 4'b0111;

  // Elaboration-time parameter checks
  initial begin
    if (n < 8) $error("lcd_driver: n (%0d) must be >= 8", n);
    if (m < 8) $error("lcd_driver: m (%0d) must be >= 8", m);
  end

  // Helper: expected out value (zero-extend/truncate)
  function automatic logic [m-1:0] exp_out8(input logic [3:0] c, input logic [3:0] d);
    if (m <= 8) exp_out8 = {c,d}[m-1:0];
    else        exp_out8 = {{(m-8){1'b0}}, c, d};
  endfunction

  default clocking cb @(posedge clk); endclocking
  // Assertions below are disabled during rst unless stated otherwise
  default disable iff (rst);

  // Reset behavior (active while rst is 1)
  assert property (@(posedge clk) rst |-> (lcd_state==STATE_INIT && lcd_row==4'd0 && lcd_col==4'd0))
    else $error("Reset did not drive INIT/row=0/col=0");

  // State encoding validity
  assert property (lcd_state inside {
      STATE_INIT, STATE_CLEAR_DISPLAY, STATE_RETURN_HOME, STATE_ENTRY_MODE_SET,
      STATE_DISPLAY_ON_OFF_CONTROL, STATE_FUNCTION_SET, STATE_WRITE_DATA, STATE_WRITE_COMMAND
    }) else $error("Illegal lcd_state value");

  // No X after reset deasserts
  assert property (!$isunknown({lcd_state,lcd_row,lcd_col,cmd_bus,data_bus})))
    else $error("Unknown (X/Z) detected on internal LCD signals");

  // Range checks
  assert property (lcd_col <= 4) else $error("lcd_col out of range (>4)");
  assert property (lcd_row <= 4'd2) else $error("lcd_row out of range (>2)");

  // Out changes only due to WRITE_COMMAND
  assert property ($changed(out) |-> $past(lcd_state)==STATE_WRITE_COMMAND)
    else $error("out changed without WRITE_COMMAND");

  // data_bus changes only due to WRITE_DATA
  assert property ($changed(data_bus) |-> $past(lcd_state)==STATE_WRITE_DATA)
    else $error("data_bus changed outside WRITE_DATA");

  // cmd_bus changes only in states that assign it
  assert property ($changed(cmd_bus) |-> ($past(lcd_state) inside {
      STATE_INIT, STATE_CLEAR_DISPLAY, STATE_RETURN_HOME,
      STATE_ENTRY_MODE_SET, STATE_DISPLAY_ON_OFF_CONTROL, STATE_FUNCTION_SET
    })) else $error("cmd_bus changed in illegal state");

  // Transitions that set cmd_bus and go to FUNCTION_SET
  assert property (lcd_state==STATE_INIT                |=> (lcd_state==STATE_FUNCTION_SET && cmd_bus==CMD_FUNCTION_SET))
    else $error("INIT transition/cmd mismatch");
  assert property (lcd_state==STATE_CLEAR_DISPLAY       |=> (lcd_state==STATE_FUNCTION_SET && cmd_bus==CMD_CLEAR_DISPLAY))
    else $error("CLEAR_DISPLAY transition/cmd mismatch");
  assert property (lcd_state==STATE_RETURN_HOME         |=> (lcd_state==STATE_FUNCTION_SET && cmd_bus==CMD_RETURN_HOME))
    else $error("RETURN_HOME transition/cmd mismatch");
  assert property (lcd_state==STATE_ENTRY_MODE_SET      |=> (lcd_state==STATE_FUNCTION_SET && cmd_bus==CMD_ENTRY_MODE_SET))
    else $error("ENTRY_MODE_SET transition/cmd mismatch");
  assert property (lcd_state==STATE_DISPLAY_ON_OFF_CONTROL |=> (lcd_state==STATE_FUNCTION_SET && cmd_bus==CMD_DISPLAY_ON_OFF_CONTROL))
    else $error("DISPLAY_ON_OFF_CONTROL transition/cmd mismatch");

  // FUNCTION_SET -> WRITE_COMMAND with proper cmd
  assert property (lcd_state==STATE_FUNCTION_SET |=> (lcd_state==STATE_WRITE_COMMAND && cmd_bus==CMD_FUNCTION_SET))
    else $error("FUNCTION_SET transition/cmd mismatch");

  // WRITE_DATA captures data[7:4] and goes to WRITE_COMMAND
  assert property (lcd_state==STATE_WRITE_DATA |=> (lcd_state==STATE_WRITE_COMMAND && data_bus==$past(data[7:4])))
    else $error("WRITE_DATA behavior mismatch");

  // WRITE_COMMAND effects: out, row/col, next-state branch
  assert property (
    lcd_state==STATE_WRITE_COMMAND |=> (
      out == exp_out8($past(cmd_bus), $past(data_bus)) &&
      // col update
      lcd_col == (($past(lcd_col)==4) ? 4'd0 : ($past(lcd_col)+4'd1)) &&
      // row update
      lcd_row == ( ($past(lcd_col)==4)
                   ? ( ($past(lcd_row)==4'd2) ? 4'd0 : ($past(lcd_row)+4'd1) )
                   : $past(lcd_row) ) &&
      // next state branch
      lcd_state == ( ($past(lcd_row)==4'd0 && $past(lcd_col)==4'd0)
                     ? STATE_CLEAR_DISPLAY : STATE_WRITE_DATA )
    ))
    else $error("WRITE_COMMAND behavior mismatch");

  // When m>8, high bits of out must be zero after WRITE_COMMAND
  generate if (m > 8) begin
    assert property ($past(lcd_state)==STATE_WRITE_COMMAND |-> out[m-1:8]=={(m-8){1'b0}})
      else $error("out upper bits not zero-extended");
  end endgenerate

  // Coverage

  // Cover visiting each state
  cover property (lcd_state==STATE_INIT);
  cover property (lcd_state==STATE_FUNCTION_SET);
  cover property (lcd_state==STATE_WRITE_COMMAND);
  cover property (lcd_state==STATE_WRITE_DATA);
  cover property (lcd_state==STATE_CLEAR_DISPLAY);
  cover property (lcd_state==STATE_RETURN_HOME);
  cover property (lcd_state==STATE_ENTRY_MODE_SET);
  cover property (lcd_state==STATE_DISPLAY_ON_OFF_CONTROL);

  // Cover WRITE_COMMAND branch to CLEAR_DISPLAY from (row=0,col=0)
  cover property (lcd_state==STATE_WRITE_COMMAND && lcd_row==0 && lcd_col==0 |=> lcd_state==STATE_CLEAR_DISPLAY);

  // Cover WRITE_COMMAND branch to WRITE_DATA when not at (0,0)
  cover property (lcd_state==STATE_WRITE_COMMAND && !(lcd_row==0 && lcd_col==0) |=> lcd_state==STATE_WRITE_DATA);

  // Cover column wrap and row increment
  cover property (lcd_state==STATE_WRITE_COMMAND && $past(lcd_col)==4 |=> lcd_col==0);

  // Cover row wrap (2 -> 0) on column wrap
  cover property (lcd_state==STATE_WRITE_COMMAND && $past(lcd_col)==4 && $past(lcd_row)==2 |=> lcd_row==0);

endmodule

// Bind SVA to the DUT
bind lcd_driver lcd_driver_sva #(.n(n), .m(m)) lcd_driver_sva_i (
  .clk(clk),
  .rst(rst),
  .data(data),
  .out(out),
  .lcd_state(lcd_state),
  .lcd_row(lcd_row),
  .lcd_col(lcd_col),
  .cmd_bus(cmd_bus),
  .data_bus(data_bus)
);