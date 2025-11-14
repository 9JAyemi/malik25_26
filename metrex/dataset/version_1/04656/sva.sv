// SVA for tmu2_pixout. Bind to the DUT.
// Focus: protocol, state transitions, data/sel mapping, capture behavior, and basic coverage.

module tmu2_pixout_sva #(parameter fml_depth=26) (
  input  logic                 sys_clk,
  input  logic                 sys_rst,

  input  logic                 pipe_stb_i,
  input  logic                 pipe_ack_o,

  input  logic [fml_depth-5-1:0] burst_addr,
  input  logic [15:0]            burst_sel,
  input  logic [255:0]           burst_do,

  input  logic [fml_depth-1:0] fml_adr,
  input  logic                 fml_stb,
  input  logic                 fml_ack,
  input  logic [7:0]           fml_sel,
  input  logic [63:0]          fml_do,

  input  logic                 busy,

  // Internal regs we want to check
  input  logic [15:0]          burst_sel_r,
  input  logic [255:0]         burst_do_r,
  input  logic                 load,
  input  logic [1:0]           state
);

  localparam IDLE  = 2'd0;
  localparam WAIT  = 2'd1;
  localparam XFER2 = 2'd2;
  localparam XFER3 = 2'd3;

  default clocking cb @(posedge sys_clk); endclocking
  default disable iff (sys_rst);

  // Basic state/output relationships
  assert property (pipe_ack_o == (state == IDLE));
  assert property (busy       == (state != IDLE));
  assert property (fml_stb    == (state == WAIT));
  assert property (fml_adr[4:0] == 5'd0);

  // Legal state transitions
  assert property ((state == IDLE  && !pipe_stb_i) |=> state == IDLE);
  assert property ((state == IDLE  &&  pipe_stb_i) |=> state == WAIT);
  assert property ((state == WAIT  && !fml_ack   ) |=> state == WAIT);
  assert property ((state == WAIT  &&  fml_ack   ) |=> state == XFER2);
  assert property ((state == XFER2)               |=> state == XFER3);
  assert property ((state == XFER3)               |=> state == IDLE);

  // Handshake acceptance only in IDLE; load pulsed on accept, and capture happens same cycle
  assert property ((state == IDLE && pipe_stb_i) |-> load);
  assert property ((state == IDLE && pipe_stb_i)
                   |-> ##0 (fml_adr == {burst_addr,5'd0}
                            && burst_sel_r == burst_sel
                            && burst_do_r  == burst_do));

  // Captured address/data/sel remain stable throughout non-IDLE states (one transaction)
  assert property ((state != IDLE) |-> $stable({fml_adr, burst_sel_r, burst_do_r}));

  // fml_stb deasserts immediately after ack cycle
  assert property ((state == WAIT && fml_ack) |=> !fml_stb);

  // Data and byte-enable mapping per chunk
  // WAIT & !ack -> chunk 0
  assert property ((state == WAIT && !fml_ack)
                   |-> (fml_stb
                        && fml_sel == {burst_sel_r[15],burst_sel_r[15],
                                        burst_sel_r[14],burst_sel_r[14],
                                        burst_sel_r[13],burst_sel_r[13],
                                        burst_sel_r[12],burst_sel_r[12]}
                        && fml_do  == burst_do_r[255:192]));

  // WAIT & ack -> chunk 1 (note: still in WAIT during the cycle ack is observed)
  assert property ((state == WAIT && fml_ack)
                   |-> (fml_stb
                        && fml_sel == {burst_sel_r[11],burst_sel_r[11],
                                        burst_sel_r[10],burst_sel_r[10],
                                        burst_sel_r[ 9],burst_sel_r[ 9],
                                        burst_sel_r[ 8],burst_sel_r[ 8]}
                        && fml_do  == burst_do_r[191:128]));

  // XFER2 -> chunk 2
  assert property ((state == XFER2)
                   |-> (!fml_stb
                        && fml_sel == {burst_sel_r[7],burst_sel_r[7],
                                        burst_sel_r[6],burst_sel_r[6],
                                        burst_sel_r[5],burst_sel_r[5],
                                        burst_sel_r[4],burst_sel_r[4]}
                        && fml_do  == burst_do_r[127:64]));

  // XFER3 -> chunk 3
  assert property ((state == XFER3)
                   |-> (!fml_stb
                        && fml_sel == {burst_sel_r[3],burst_sel_r[3],
                                        burst_sel_r[2],burst_sel_r[2],
                                        burst_sel_r[1],burst_sel_r[1],
                                        burst_sel_r[0],burst_sel_r[0]}
                        && fml_do  == burst_do_r[63:0]));

  // No accept/load outside IDLE
  assert property ((state != IDLE) |-> (!pipe_ack_o && !load));

  // Coverage: typical and edge transactions
  sequence handshake; state == IDLE && pipe_stb_i && pipe_ack_o; endsequence
  sequence stall_wait; state == WAIT && fml_stb && !fml_ack; endsequence

  // Typical: handshake, stall >=1, ack, then XFER2->XFER3->IDLE
  cover property (handshake ##1 stall_wait[*1:$] ##1
                  (state == WAIT && fml_ack) ##1
                  state == XFER2 ##1 state == XFER3 ##1 state == IDLE);

  // No-stall: ack on first WAIT cycle
  cover property (handshake ##1 (state == WAIT && fml_stb && fml_ack)
                  ##1 state == XFER2 ##1 state == XFER3 ##1 state == IDLE);

  // Back-to-back transactions
  cover property (handshake ##1 state == WAIT ##[1:$] state == IDLE ##1 handshake);

endmodule

// Example bind (instantiate in your testbench or a bind file):
// bind tmu2_pixout tmu2_pixout_sva #(.fml_depth(fml_depth)) sva (
//   .sys_clk(sys_clk), .sys_rst(sys_rst),
//   .pipe_stb_i(pipe_stb_i), .pipe_ack_o(pipe_ack_o),
//   .burst_addr(burst_addr), .burst_sel(burst_sel), .burst_do(burst_do),
//   .fml_adr(fml_adr), .fml_stb(fml_stb), .fml_ack(fml_ack), .fml_sel(fml_sel), .fml_do(fml_do),
//   .busy(busy),
//   .burst_sel_r(burst_sel_r), .burst_do_r(burst_do_r), .load(load), .state(state)
// );