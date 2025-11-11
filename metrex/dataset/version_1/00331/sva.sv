// SVA for memory_interface: concise, high-value checks and coverage.
// Bind this into the DUT; it references internal nets.
module memory_interface_sva #(
  parameter AW = 12,
  parameter DW = 32
)(
  input  clk,
  input  rst_n,

  // DUT ports
  input        icb_cmd_valid,
  input        icb_cmd_ready,
  input  [AW-1:0] icb_cmd_addr,
  input        icb_cmd_read,
  input        icb_rsp_ready,
  input        icb_rsp_valid,
  input        icb_rsp_err,
  input  [DW-1:0] icb_rsp_rdata,

  // DUT internal nets
  input        mem_we,
  input  [AW-1:0] mem_addr,
  input  [DW-1:0] mem_dout,
  input  [DW-1:0] mem_din
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Structural/comb connectivity
  assert property (icb_cmd_ready) else $error("icb_cmd_ready must be 1");
  assert property (icb_rsp_err == 1'b0);
  assert property (icb_rsp_valid == (icb_cmd_valid && icb_cmd_ready));
  assert property (icb_rsp_rdata == mem_dout);
  assert property (mem_we == ~icb_cmd_read);
  assert property ({mem_addr[AW-1:2], mem_addr[1:0]} == {icb_cmd_addr[AW-1:2], 2'b00});
  assert property (icb_cmd_read |-> (mem_din == '0));
  assert property (!icb_cmd_read |-> (mem_din == icb_rsp_rdata && icb_rsp_rdata == mem_dout));

  // X-prop hygiene
  assert property (!$isunknown({icb_cmd_ready, icb_rsp_valid, icb_rsp_err})); 
  assert property (icb_rsp_valid |-> !$isunknown(icb_rsp_rdata));
  assert property (!$isunknown({mem_we, mem_addr, mem_din}));

  // Response must be held/stable under backpressure (typical protocol requirement)
  assert property ((icb_rsp_valid && !icb_rsp_ready) |=> icb_rsp_valid);
  assert property ((icb_rsp_valid && !icb_rsp_ready) |=> $stable(icb_rsp_rdata));

  // Synchronous memory behavior: write does not change dout at the same edge
  assert property (mem_we |-> $stable(mem_dout));

  // Timing: a read command should return a response on the next cycle with the addressed data.
  // Also requires the addressed mem_addr to be presented for the read-return cycle.
  // This will flag the current single-cycle rsp_valid wiring and missing address hold.
  property p_read_latency_and_addr_hold;
    logic [AW-1:0] a;
    (icb_cmd_valid && icb_cmd_ready && icb_cmd_read, a = mem_addr)
      |=> (icb_rsp_valid && (mem_addr == a));
  endproperty
  assert property (p_read_latency_and_addr_hold);

  // Optional: writes should be qualified by a valid command (flags ungated mem_we)
  assert property (mem_we |-> icb_cmd_valid);

  // Coverage: basic transactions, corner cases
  cover property (icb_cmd_valid && icb_cmd_ready && icb_cmd_read);           // read
  cover property (icb_cmd_valid && icb_cmd_ready && !icb_cmd_read);          // write
  cover property ((icb_cmd_valid && icb_cmd_ready && icb_cmd_read)
                  ##1 (icb_cmd_valid && icb_cmd_ready && icb_cmd_read));     // back-to-back reads
  cover property ((icb_rsp_valid && !icb_rsp_ready)
                  ##1 (icb_rsp_valid && !icb_rsp_ready));                    // sustained backpressure
  cover property (icb_cmd_valid && icb_cmd_ready && (|icb_cmd_addr[1:0]));   // unaligned addr seen

endmodule

// Bind into DUT (instantiate once in your testbench or a bind file)
bind memory_interface memory_interface_sva #(.AW(AW), .DW(DW)) u_sva (
  .clk(clk),
  .rst_n(rst_n),
  .icb_cmd_valid(icb_cmd_valid),
  .icb_cmd_ready(icb_cmd_ready),
  .icb_cmd_addr(icb_cmd_addr),
  .icb_cmd_read(icb_cmd_read),
  .icb_rsp_ready(icb_rsp_ready),
  .icb_rsp_valid(icb_rsp_valid),
  .icb_rsp_err(icb_rsp_err),
  .icb_rsp_rdata(icb_rsp_rdata),
  .mem_we(mem_we),
  .mem_addr(mem_addr),
  .mem_dout(mem_dout),
  .mem_din(mem_din)
);