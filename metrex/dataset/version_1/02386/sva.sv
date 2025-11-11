// SVA for joypad_controller
module joypad_controller_sva #(
  parameter logic [15:0] ADDR = 16'hFF00
)(
  input  logic        clock,
  input  logic        reset,
  input  logic        int_ack,   // unused in RTL, covered minimally
  input  logic        int_req,
  input  logic [15:0] A,
  input  logic  [7:0] Di,
  input  logic  [7:0] Do,
  input  logic        rd_n,
  input  logic        wr_n,
  input  logic        cs,
  input  logic  [1:0] button_sel,
  input  logic  [3:0] button_data
);

  default clocking cb @(posedge clock); endclocking
  default disable iff (reset);

  // Writes to FF00 update button_sel on next cycle with Di[5:4]
  assert property ( (!wr_n && A == ADDR) |=> button_sel == $past(Di[5:4]) );

  // In all other cycles, button_sel holds its value
  assert property ( !(!wr_n && A == ADDR) |=> $stable(button_sel) );

  // Data output mapping when selected
  assert property ( cs |-> (Do == {2'b11, button_sel, button_data}) );

  // Default value when not selected
  assert property ( !cs |-> (Do == 8'hFF) );

  // Interrupt: must be 0 during reset and never assert afterward (matches RTL)
  assert property ( reset |-> (int_req == 1'b0) );
  assert property ( !int_req );

  // Optional sanity: no simultaneous read and write
  assert property ( !(!rd_n && !wr_n) );

  // ------------- Functional coverage -------------
  // Exercise all button_sel encodings via writes
  cover property ( (!wr_n && A == ADDR && Di[5:4] == 2'b00) );
  cover property ( (!wr_n && A == ADDR && Di[5:4] == 2'b01) );
  cover property ( (!wr_n && A == ADDR && Di[5:4] == 2'b10) );
  cover property ( (!wr_n && A == ADDR && Di[5:4] == 2'b11) );

  // Observe button_sel changing
  cover property ( $changed(button_sel) );

  // Observe output behavior in both CS states
  cover property ( cs && (Do == {2'b11, button_sel, button_data}) );
  cover property ( !cs && (Do == 8'hFF) );

  // See a variety of button_data reflected in Do when selected
  cover property ( cs && button_data == 4'h0 );
  cover property ( cs && button_data == 4'hF );

  // See an int_ack pulse (input exercised even if unused)
  cover property ( $rose(int_ack) );

endmodule

// Bind into the DUT
bind joypad_controller joypad_controller_sva sva_inst (
  .clock(clock),
  .reset(reset),
  .int_ack(int_ack),
  .int_req(int_req),
  .A(A),
  .Di(Di),
  .Do(Do),
  .rd_n(rd_n),
  .wr_n(wr_n),
  .cs(cs),
  .button_sel(button_sel),
  .button_data(button_data)
);