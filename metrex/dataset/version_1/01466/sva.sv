// SVA for uart_tx
// Bindable checker focusing on protocol, timing, state machine, bit ordering, and tx_done semantics.

module uart_tx_sva
  #(parameter string RTX_EXTERNAL_OVERRIDE = "NO")
  (
    input  logic        clk_i, rst_i,
    input  logic        tx_start_i, locked_i,
    input  logic [28:0] bitperiod_i,
    input  logic [7:0]  din_bi,
    input  logic        tx_done_tick_o, tx_o,

    // Internal DUT signals (for bind)
    input  logic [3:0]  state,
    input  logic [7:0]  databuf,
    input  logic [31:0] clk_counter,
    input  logic [2:0]  bit_counter
  );

  // Mirror DUT constants
  localparam [7:0] ST_IDLE    = 8'h0;
  localparam [7:0] ST_START   = 8'h1;
  localparam [7:0] ST_TX_DATA = 8'h2;
  localparam [7:0] ST_STOP    = 8'h3;

  // Convenience compares
  wire [31:0] BP  = {3'h0, bitperiod_i};
  wire [31:0] BP2 = {2'h0, bitperiod_i, 1'b0};

  default clocking cb @(posedge clk_i); endclocking
  default disable iff (rst_i);

  // Sanity / reset
  ap_reset: assert property (rst_i |=> (state==ST_IDLE && databuf==8'h0 && clk_counter==32'h0 && tx_o==1'b1 && tx_done_tick_o==1'b0));
  ap_state_valid: assert property (1'b1 |-> (state inside {ST_IDLE,ST_START,ST_TX_DATA,ST_STOP}));
  ap_no_x: assert property (!$isunknown({state, tx_o, tx_done_tick_o}));

  // IDLE behavior
  ap_idle_tx_high: assert property ((state==ST_IDLE) |-> (tx_o==1'b1));
  ap_idle_counter_zero: assert property ((state==ST_IDLE) |-> (clk_counter==32'h0));
  ap_start_requires_locked: assert property ((state==ST_IDLE && tx_start_i && !locked_i) |=> (state==ST_IDLE));
  ap_idle_to_start: assert property (
    (state==ST_IDLE && tx_start_i && locked_i)
    |=> (state==ST_START && tx_o==1'b0 && databuf==$past(din_bi) && clk_counter==32'h0)
  );

  // START bit timing and invariants
  ap_start_tx_low: assert property ((state==ST_START) |-> (tx_o==1'b0));
  ap_start_cnt_inc: assert property ((state==ST_START && clk_counter!=BP) |=> (state==ST_START && clk_counter==$past(clk_counter)+1));
  ap_start_stay_until_bp: assert property ((state==ST_START && clk_counter!=BP) |=> (state==ST_START));
  ap_start_to_data_boundary: assert property (
    (state==ST_START && clk_counter==BP)
    |=> (state==ST_TX_DATA && clk_counter==32'h0 && bit_counter==3'h0 &&
         tx_o==$past(databuf[0]) && databuf=={1'b0,$past(databuf[7:1])})
  );

  // DATA bit timing and shifting
  ap_data_hold_when_not_boundary: assert property (
    (state==ST_TX_DATA && clk_counter!=BP)
    |=> (state==ST_TX_DATA && tx_o==$past(tx_o) && clk_counter==$past(clk_counter)+1)
  );

  // Next data bit (not last)
  ap_data_nextbit: assert property (
    (state==ST_TX_DATA && clk_counter==BP && $past(bit_counter)!=3'h7)
    |=> (state==ST_TX_DATA && clk_counter==32'h0 &&
         bit_counter==$past(bit_counter)+1 &&
         tx_o==$past(databuf[0]) &&
         databuf=={1'b0,$past(databuf[7:1])})
  );

  // Last data bit -> STOP
  ap_data_to_stop: assert property (
    (state==ST_TX_DATA && clk_counter==BP && $past(bit_counter)==3'h7)
    |=> (state==ST_STOP && clk_counter==32'h0 && tx_o==1'b1)
  );

  // STOP bit timing (2 bit periods) and exit
  ap_stop_tx_high: assert property ((state==ST_STOP) |-> (tx_o==1'b1));
  ap_stop_cnt_inc: assert property ((state==ST_STOP && clk_counter!=BP2) |=> (state==ST_STOP && clk_counter==$past(clk_counter)+1));
  ap_stop_stay_until_bp2: assert property ((state==ST_STOP && clk_counter!=BP2) |=> (state==ST_STOP));
  ap_stop_exit_next: assert property ((state==ST_STOP && clk_counter==BP2) |=> (state==ST_IDLE));
  ap_stop_exit_done_pulse: assert property ((state==ST_STOP && clk_counter==BP2) |-> (tx_done_tick_o==1'b1));

  // bit_counter only changes in TX_DATA at boundary (it initializes on entry to TX_DATA)
  ap_bcnt_stable_outside_data: assert property ((state!=ST_TX_DATA) |=> (bit_counter==$past(bit_counter)));

  // tx_done semantics vs RTX_EXTERNAL_OVERRIDE
  generate
    if (RTX_EXTERNAL_OVERRIDE == "NO") begin
      ap_done_zero_when_not_stop: assert property ((state!=ST_STOP) |-> (tx_done_tick_o==1'b0));
      // Pulse only on STOP exit cycle already checked by ap_stop_exit_done_pulse
    end else begin
      ap_done_always_one_when_not_reset: assert property ((!rst_i) |-> (tx_done_tick_o==1'b1));
    end
  endgenerate

  // Coverage
  // 1) Full transaction path
  cp_tx_path: cover property (
    (state==ST_IDLE && tx_start_i && locked_i)
    ##1 (state==ST_START)
    ##[1:$] (state==ST_TX_DATA)
    ##[1:$] (state==ST_STOP)
    ##1 (state==ST_IDLE)
  );

  // 2) See both data bit values driven at TX_DATA boundaries
  cp_data0: cover property (state==ST_TX_DATA && clk_counter==BP && $past(bit_counter)!=3'h7 && $past(databuf[0])==1'b0);
  cp_data1: cover property (state==ST_TX_DATA && clk_counter==BP && $past(bit_counter)!=3'h7 && $past(databuf[0])==1'b1);

  // 3) Observe tx_done pulse
  cp_done_pulse: cover property (state==ST_STOP && clk_counter==BP2 && tx_done_tick_o);

endmodule

// Bind into DUT
bind uart_tx uart_tx_sva #(.RTX_EXTERNAL_OVERRIDE(RTX_EXTERNAL_OVERRIDE)) uart_tx_sva_b (
  .clk_i(clk_i),
  .rst_i(rst_i),
  .tx_start_i(tx_start_i),
  .locked_i(locked_i),
  .bitperiod_i(bitperiod_i),
  .din_bi(din_bi),
  .tx_done_tick_o(tx_done_tick_o),
  .tx_o(tx_o),
  .state(state),
  .databuf(databuf),
  .clk_counter(clk_counter),
  .bit_counter(bit_counter)
);