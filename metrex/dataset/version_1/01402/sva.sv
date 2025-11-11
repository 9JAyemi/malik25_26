// SVA checker for csrbrg
module csrbrg_sva
(
  input  logic        sys_clk,
  input  logic        sys_rst,

  input  logic [31:0] wb_adr_i,
  input  logic [31:0] wb_dat_i,
  input  logic        wb_cyc_i,
  input  logic        wb_stb_i,
  input  logic        wb_we_i,
  input  logic        wb_ack_o,
  input  logic [31:0] wb_dat_o,

  input  logic [13:0] csr_a,
  input  logic        csr_we,
  input  logic [31:0] csr_do,
  input  logic [31:0] csr_di,

  input  logic [1:0]  state
);

  // Mirror DUT encoding
  localparam IDLE       = 2'd0;
  localparam DELAYACK1  = 2'd1;
  localparam DELAYACK2  = 2'd2;
  localparam ACK        = 2'd3;

  default clocking cb @(posedge sys_clk); endclocking
  default disable iff (sys_rst);

  // Handy sequences
  sequence idle_wr_req; state==IDLE && wb_cyc_i && wb_stb_i && wb_we_i; endsequence
  sequence idle_rd_req; state==IDLE && wb_cyc_i && wb_stb_i && !wb_we_i; endsequence

  // ACK only in ACK state, and always in ACK state (combinational decode)
  assert property (wb_ack_o |-> state==ACK);
  assert property (state==ACK |-> wb_ack_o);

  // ACK is a single-cycle pulse
  assert property (wb_ack_o |=> !wb_ack_o);

  // Deterministic state transitions
  assert property ((state==IDLE      && !(wb_cyc_i && wb_stb_i)) |=> state==IDLE);
  assert property ( idle_wr_req                                       |=> state==ACK);
  assert property ( idle_rd_req                                       |=> state==DELAYACK1);
  assert property ((state==DELAYACK1)                                 |=> state==DELAYACK2);
  assert property ((state==DELAYACK2)                                 |=> state==ACK);
  assert property ((state==ACK)                                       |=> state==IDLE);

  // ACK timing relative to request
  assert property ( idle_wr_req |=> wb_ack_o);                                  // write: 1-cycle latency
  assert property ( idle_rd_req |=> !wb_ack_o ##1 !wb_ack_o ##1 wb_ack_o);      // read: 3rd cycle ACK

  // ACK must occur only under CYC
  assert property (wb_ack_o |-> wb_cyc_i);

  // ACK causality: must be due to a prior request (write 1-cycle ago, read 3-cycles ago)
  assert property (wb_ack_o |-> ($past(idle_wr_req,1) || $past(idle_rd_req,3)));

  // CSR write strobe: one-cycle pulse right after a write request in IDLE; never on reads
  assert property ( idle_wr_req |=> (csr_we && ##1 !csr_we));
  assert property ( csr_we |-> $past(idle_wr_req,1));
  assert property ( idle_rd_req |=> !csr_we ##1 !csr_we); // ensure no accidental write on read path

  // Registered datapath relationships
  assert property (wb_dat_o == $past(csr_di));
  assert property (csr_do   == $past(wb_dat_i));
  assert property (csr_a    == $past(wb_adr_i[15:2]));

  // Functional coverage
  cover property ( idle_wr_req ##1 wb_ack_o ##1 state==IDLE );                    // write request and ack
  cover property ( idle_rd_req ##3 wb_ack_o ##1 state==IDLE );                    // read request and ack
  cover property ( idle_wr_req ##1 wb_ack_o ##1 idle_rd_req ##3 wb_ack_o );       // write then read
  cover property ( idle_rd_req ##3 wb_ack_o ##1 idle_wr_req ##1 wb_ack_o );       // read then write
endmodule

// Bind into DUT
bind csrbrg csrbrg_sva sva_i (.*,.state(state));