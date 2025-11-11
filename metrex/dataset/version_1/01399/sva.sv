// SVA for pcie_7x_v1_8_gtp_pipe_rate
// Bind this module to the DUT instance
// Example: bind pcie_7x_v1_8_gtp_pipe_rate pcie_7x_v1_8_gtp_pipe_rate_sva #(.TXDATA_WAIT_MAX(TXDATA_WAIT_MAX)) i_rate_sva();

module pcie_7x_v1_8_gtp_pipe_rate_sva #(parameter int TXDATA_WAIT_MAX = 15) ();

  // Local mirror of FSM encodings (must match DUT)
  localparam [7:0] FSM_IDLE         = 8'b00000001;
  localparam [7:0] FSM_TXDATA_WAIT  = 8'b00000010;
  localparam [7:0] FSM_PCLK_SEL     = 8'b00000100;
  localparam [7:0] FSM_RATE_SEL     = 8'b00001000;
  localparam [7:0] FSM_RATE_DONE    = 8'b00010000;
  localparam [7:0] FSM_TXSYNC_START = 8'b00100000;
  localparam [7:0] FSM_TXSYNC_DONE  = 8'b01000000;
  localparam [7:0] FSM_DONE         = 8'b10000000;

  default clocking cb @(posedge RATE_CLK); endclocking
  default disable iff (!RATE_RST_N)

  // Reset values
  assert property (@(posedge RATE_CLK) !RATE_RST_N |-> (fsm==FSM_IDLE && pclk_sel==1'b0 && rate_out==3'd0 &&
                                                        txdata_wait_cnt==4'd0 && !txratedone && !rxratedone &&
                                                        !phystatus && !ratedone));

  // Onehot FSM and legal encodings
  assert property ($onehot(fsm));

  // Input double-flop behavior
  assert property (rst_idle_reg2    == $past(rst_idle_reg1));
  assert property (rate_in_reg2     == $past(rate_in_reg1));
  assert property (txratedone_reg2  == $past(txratedone_reg1));
  assert property (rxratedone_reg2  == $past(rxratedone_reg1));
  assert property (phystatus_reg2   == $past(phystatus_reg1));
  assert property (txsync_done_reg2 == $past(txsync_done_reg1));

  // Combinational rate decode
  assert property (rate == ((rate_in_reg2==2'd1) ? 3'd1 : 3'd0));

  // IDLE transitions
  assert property ((fsm==FSM_IDLE && (rate_in_reg2 != rate_in_reg1)) |=> (fsm==FSM_TXDATA_WAIT));
  assert property ((fsm==FSM_IDLE && (rate_in_reg2 == rate_in_reg1)) |=> (fsm==FSM_IDLE));

  // TXDATA_WAIT counter behavior and exit
  assert property ((fsm==FSM_TXDATA_WAIT && txdata_wait_cnt <  TXDATA_WAIT_MAX) |=> (txdata_wait_cnt == $past(txdata_wait_cnt)+1));
  assert property ((fsm==FSM_TXDATA_WAIT && txdata_wait_cnt == TXDATA_WAIT_MAX) |=> (txdata_wait_cnt == $past(txdata_wait_cnt) && fsm==FSM_PCLK_SEL));
  assert property ((fsm!=FSM_TXDATA_WAIT) |=> (txdata_wait_cnt==0));
  assert property (txdata_wait_cnt <= TXDATA_WAIT_MAX);

  // PCLK_SEL update and transition
  assert property ((fsm==FSM_PCLK_SEL) |=> (fsm==FSM_RATE_SEL && pclk_sel == (rate_in_reg2==2'd1)));
  assert property ($changed(pclk_sel) |-> $past(fsm)==FSM_PCLK_SEL);

  // RATE_SEL update and transition
  assert property ((fsm==FSM_RATE_SEL) |=> (fsm==FSM_RATE_DONE && rate_out == rate));
  assert property ($changed(rate_out) |-> $past(fsm)==FSM_RATE_SEL);

  // RATE_DONE sticky accumulation and transition
  assert property ((fsm==FSM_RATE_DONE && txratedone_reg2) |=> txratedone);
  assert property ((fsm==FSM_RATE_DONE && rxratedone_reg2) |=> rxratedone);
  assert property ((fsm==FSM_RATE_DONE && phystatus_reg2) |=> phystatus);
  assert property ((fsm==FSM_RATE_DONE && $past(txratedone)) |=> txratedone);
  assert property ((fsm==FSM_RATE_DONE && $past(rxratedone)) |=> rxratedone);
  assert property ((fsm==FSM_RATE_DONE && $past(phystatus))  |=> phystatus);
  assert property ((fsm==FSM_RATE_DONE && txratedone && rxratedone && phystatus) |=> ratedone);
  assert property ((fsm==FSM_RATE_DONE && ratedone) |-> (txratedone && rxratedone && phystatus));
  assert property ((fsm==FSM_RATE_DONE && ratedone) |=> (fsm==FSM_TXSYNC_START));
  assert property ((fsm==FSM_RATE_DONE && !ratedone) |=> (fsm==FSM_RATE_DONE));
  assert property (($past(fsm)==FSM_RATE_DONE && fsm!=FSM_RATE_DONE) |-> (!txratedone && !rxratedone && !phystatus && !ratedone));

  // TXSYNC_START/DONE handshakes
  assert property ((fsm==FSM_TXSYNC_START && !txsync_done_reg2) |=> (fsm==FSM_TXSYNC_DONE));
  assert property ((fsm==FSM_TXSYNC_START &&  txsync_done_reg2) |=> (fsm==FSM_TXSYNC_START));
  assert property ((fsm==FSM_TXSYNC_DONE  &&  txsync_done_reg2) |=> (fsm==FSM_DONE));
  assert property ((fsm==FSM_TXSYNC_DONE  && !txsync_done_reg2) |=> (fsm==FSM_TXSYNC_DONE));

  // DONE -> IDLE
  assert property ((fsm==FSM_DONE) |=> (fsm==FSM_IDLE));

  // Output mappings
  assert property (RATE_PCLK_SEL     == pclk_sel);
  assert property (RATE_RATE_OUT     == rate_out);
  assert property (RATE_TXSYNC_START == (fsm==FSM_TXSYNC_START));
  assert property (RATE_DONE         == (fsm==FSM_DONE));
  assert property (RATE_IDLE         == (fsm==FSM_IDLE));
  assert property (RATE_FSM[7:0]     == fsm);
  assert property (RATE_FSM[23:8]    == '0);

  // Coverage: full successful rate change path (with txsync_done 0->1 handshake)
  cover property (
    (fsm==FSM_IDLE && rate_in_reg2!=rate_in_reg1)
    ##1 fsm==FSM_TXDATA_WAIT
    ##[1:$] (txdata_wait_cnt==TXDATA_WAIT_MAX && fsm==FSM_PCLK_SEL)
    ##1 fsm==FSM_RATE_SEL
    ##1 fsm==FSM_RATE_DONE
    ##[1:$] ratedone
    ##1 fsm==FSM_TXSYNC_START
    ##1 !txsync_done_reg2
    ##1 fsm==FSM_TXSYNC_DONE
    ##[1:$] (txsync_done_reg2 && fsm==FSM_DONE)
    ##1 fsm==FSM_IDLE
  );

  // Coverage: alternate txsync_done stuck-high then toggle 1->0->1 path
  cover property (
    (fsm==FSM_RATE_DONE && ratedone)
    ##1 fsm==FSM_TXSYNC_START
    ##[1:5] (txsync_done_reg2 && fsm==FSM_TXSYNC_START)
    ##1 (!txsync_done_reg2 && fsm==FSM_TXSYNC_DONE)
    ##[1:5] (txsync_done_reg2 && fsm==FSM_DONE)
    ##1 fsm==FSM_IDLE
  );

endmodule