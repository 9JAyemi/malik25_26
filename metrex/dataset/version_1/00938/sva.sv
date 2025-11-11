// SVA for module recepcion
// Bind example (place in a package or alongside the DUT):
// bind recepcion recepcion_sva i_recepcion_sva (.clk_div(clk_div), .rx(rx), .avail(avail), .dout(dout), .state(state), .bitpos(bitpos), .scratch(scratch));

module recepcion_sva(
  input logic        clk_div,
  input logic        rx,
  input logic        avail,
  input logic [7:0]  dout,
  input logic [1:0]  state,
  input logic [3:0]  bitpos,
  input logic [7:0]  scratch
);
  localparam RX_STATE_START = 2'b00;
  localparam RX_STATE_DATA  = 2'b01;
  localparam RX_STATE_STOP  = 2'b10;

  default clocking cb @(negedge clk_div); endclocking

  // Basic invariants
  assert property (state inside {RX_STATE_START,RX_STATE_DATA,RX_STATE_STOP});
  assert property (bitpos <= 4'd8);

  // START detect -> enter DATA with cleared bitpos/scratch, avail low next cycle
  assert property ((state==RX_STATE_START && rx==1'b0)
                   |=> (state==RX_STATE_DATA && bitpos==4'd0 && scratch==8'h00 && !avail));

  // DATA: when bitpos<=7, increment and capture rx into correct bit
  assert property ((state==RX_STATE_DATA && bitpos<=4'd7)
                   |=> (bitpos==$past(bitpos)+1 && scratch[$past(bitpos)]==$past(rx)));

  // DATA: when bitpos==8, go to STOP and hold bitpos
  assert property ((state==RX_STATE_DATA && bitpos==4'd8)
                   |=> (state==RX_STATE_STOP && bitpos==4'd8));

  // STOP: while rx==0, remain in STOP, no avail, dout stable
  assert property ((state==RX_STATE_STOP && rx==1'b0)
                   |=> (state==RX_STATE_STOP && !avail && $stable(dout)));

  // STOP release (rx==1): next cycle pulse avail, move to START, update dout from last scratch
  assert property ((state==RX_STATE_STOP && rx==1'b1)
                   |=> (state==RX_STATE_START && avail && dout==$past(scratch)));

  // Avail is a single-cycle pulse
  assert property (avail |=> !avail);

  // Avail only asserted as a result of STOP with rx==1
  assert property (avail |-> $past(state==RX_STATE_STOP && rx==1'b1));

  // Dout only changes on STOP->START update
  assert property ($changed(dout) |-> $past(state==RX_STATE_STOP && rx==1'b1));

  // Scratch only changes while capturing data bits
  assert property ($changed(scratch) |-> $past(state==RX_STATE_DATA && bitpos<=4'd7));

  // Coverage: complete byte reception with avail pulse
  cover property ((state==RX_STATE_START && rx==1'b0)
                  ##1 (state==RX_STATE_DATA && bitpos==4'd0)
                  ##[7] (state==RX_STATE_DATA && bitpos==4'd8)
                  ##1 (state==RX_STATE_STOP)
                  ##[1:$] (state==RX_STATE_STOP && rx==1'b1)
                  ##1 (state==RX_STATE_START && avail));

  // Coverage: STOP can wait multiple cycles before release
  cover property ((state==RX_STATE_STOP && rx==1'b0) ##[2:$] (state==RX_STATE_STOP && rx==1'b1));
endmodule