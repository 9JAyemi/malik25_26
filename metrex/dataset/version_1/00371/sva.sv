// SVA for minimac2_tx
// Bind module that checks key protocol, state machine, counters, and MII pipeline behavior.

module minimac2_tx_sva
  #(parameter int ADDR_W = 11)
(
  input  logic                 clk,

  // DUT ports
  input  logic                 tx_start,
  input  logic                 tx_done,
  input  logic [ADDR_W-1:0]    tx_count,
  input  logic [7:0]           txb_dat,
  input  logic [ADDR_W-1:0]    txb_adr,
  input  logic                 phy_tx_en,
  input  logic [3:0]           phy_tx_data,

  // DUT internals
  input  logic [1:0]           state,
  input  logic [1:0]           next_state,
  input  logic                 phy_tx_en_r,
  input  logic                 phy_tx_data_sel,
  input  logic [ADDR_W-1:0]    byte_count,
  input  logic                 byte_count_reset,
  input  logic                 byte_count_inc,
  input  logic                 byte_count_max,
  input  logic [3:0]           phy_tx_data_r
);

  // state encodings (must match DUT)
  localparam logic [1:0] IDLE      = 2'd0;
  localparam logic [1:0] SEND_LO   = 2'd1;
  localparam logic [1:0] SEND_HI   = 2'd2;
  localparam logic [1:0] TERMINATE = 2'd3;

  // past-valid for disable iff
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // 0) Basic sanity
  // First observed cycle after sim start should be IDLE
  assert property (@(posedge clk) disable iff(!past_valid)
                   $rose(past_valid) |-> state == IDLE);

  // Legal state encoding
  assert property (@(posedge clk) disable iff(!past_valid)
                   state inside {IDLE,SEND_LO,SEND_HI,TERMINATE});

  // 1) Next-state logic correctness
  assert property (@(posedge clk) disable iff(!past_valid) (state==IDLE &&  tx_start) |-> next_state==SEND_LO);
  assert property (@(posedge clk) disable iff(!past_valid) (state==IDLE && !tx_start) |-> next_state==IDLE);
  assert property (@(posedge clk) disable iff(!past_valid)  state==SEND_LO               |-> next_state==SEND_HI);
  assert property (@(posedge clk) disable iff(!past_valid) (state==SEND_HI &&  byte_count_max) |-> next_state==TERMINATE);
  assert property (@(posedge clk) disable iff(!past_valid) (state==SEND_HI && !byte_count_max) |-> next_state==SEND_LO);
  assert property (@(posedge clk) disable iff(!past_valid)  state==TERMINATE            |-> next_state==IDLE);

  // State register follows next_state
  assert property (@(posedge clk) disable iff(!past_valid)
                   state == $past(next_state));

  // 2) Counter and address behavior
  // Byte counter operations per state
  assert property (@(posedge clk) disable iff(!past_valid)
                   $past(state)==SEND_LO |-> byte_count == $past(byte_count)+1);
  assert property (@(posedge clk) disable iff(!past_valid)
                   $past(state)==SEND_HI |-> byte_count == $past(byte_count));
  assert property (@(posedge clk) disable iff(!past_valid)
                   $past(state) inside {IDLE,TERMINATE} |-> byte_count == '0);

  // No overflow beyond programmed count (design intent)
  assert property (@(posedge clk) disable iff(!past_valid)
                   byte_count <= tx_count);

  // Definition of max flag
  assert property (@(posedge clk) disable iff(!past_valid)
                   byte_count_max <-> (byte_count == tx_count));

  // Address mirrors byte_count and resets in IDLE
  assert property (@(posedge clk) disable iff(!past_valid)
                   txb_adr == byte_count);
  assert property (@(posedge clk) disable iff(!past_valid)
                   state==IDLE |-> txb_adr == '0);

  // 3) Output enable/data pipeline and selection
  // Combinational control per state
  assert property (@(posedge clk) disable iff(!past_valid)
                   phy_tx_en_r == (state inside {SEND_LO,SEND_HI}));
  assert property (@(posedge clk) disable iff(!past_valid)
                   phy_tx_data_sel == (state==SEND_HI));

  // 1-cycle pipeline from *_r to outputs
  assert property (@(posedge clk) disable iff(!past_valid)
                   phy_tx_en == $past(phy_tx_en_r));
  assert property (@(posedge clk) disable iff(!past_valid)
                   phy_tx_data == $past(phy_tx_data_r));

  // When transmitting, nibble mapping matches selector and previous txb_dat
  assert property (@(posedge clk) disable iff(!past_valid)
                   $past(state)==SEND_LO |-> phy_tx_en && (phy_tx_data == $past(txb_dat[3:0])));
  assert property (@(posedge clk) disable iff(!past_valid)
                   $past(state)==SEND_HI |-> phy_tx_en && (phy_tx_data == $past(txb_dat[7:4])));
  // When idle/terminate previously, output enable must be low
  assert property (@(posedge clk) disable iff(!past_valid)
                   $past(state) inside {IDLE,TERMINATE} |-> !phy_tx_en);

  // 4) tx_done pulse semantics
  // tx_done asserted iff in TERMINATE
  assert property (@(posedge clk) disable iff(!past_valid)
                   tx_done == (state==TERMINATE));
  // Single-cycle pulse
  assert property (@(posedge clk) disable iff(!past_valid)
                   tx_done |=> !tx_done);
  // Termination must follow a SEND_HI
  assert property (@(posedge clk) disable iff(!past_valid)
                   tx_done |-> $past(state)==SEND_HI);
  // After tx_done, we return to IDLE with counter cleared
  assert property (@(posedge clk) disable iff(!past_valid)
                   tx_done |=> (state==IDLE && byte_count=='0 && txb_adr=='0));

  // 5) Protocol sanity: disallow zero-length start (design would hang)
  assert property (@(posedge clk) disable iff(!past_valid)
                   (state==IDLE && tx_start) |-> (tx_count > 0));

  // 6) Liveness: any valid start eventually completes
  assert property (@(posedge clk) disable iff(!past_valid)
                   (state==IDLE && tx_start && (tx_count>0)) |-> ##[1:$] tx_done);

  // 7) Minimal coverage
  // Cover 1-byte transfer
  cover property (@(posedge clk) disable iff(!past_valid)
                  (state==IDLE && tx_start && tx_count==ADDR_W'(11'd1))
                  ##1 state==SEND_LO ##1 state==SEND_HI ##1 state==TERMINATE ##1 state==IDLE);

  // Cover multi-byte transfer (>=2)
  cover property (@(posedge clk) disable iff(!past_valid)
                  (state==IDLE && tx_start && tx_count>=ADDR_W'(11'd2))
                  ##1 state==SEND_LO ##1 state==SEND_HI ##1 state==SEND_LO ##1 state==SEND_HI ##[1:$] tx_done);

  // Cover back-to-back transfers
  cover property (@(posedge clk) disable iff(!past_valid)
                  tx_done ##1 (state==IDLE && tx_start));

endmodule

// Bind SVA to DUT
bind minimac2_tx minimac2_tx_sva #(.ADDR_W(11)) u_minimac2_tx_sva (
  .clk              (phy_tx_clk),

  .tx_start         (tx_start),
  .tx_done          (tx_done),
  .tx_count         (tx_count),
  .txb_dat          (txb_dat),
  .txb_adr          (txb_adr),
  .phy_tx_en        (phy_tx_en),
  .phy_tx_data      (phy_tx_data),

  .state            (state),
  .next_state       (next_state),
  .phy_tx_en_r      (phy_tx_en_r),
  .phy_tx_data_sel  (phy_tx_data_sel),
  .byte_count       (byte_count),
  .byte_count_reset (byte_count_reset),
  .byte_count_inc   (byte_count_inc),
  .byte_count_max   (byte_count_max),
  .phy_tx_data_r    (phy_tx_data_r)
);