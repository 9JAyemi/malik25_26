// SVA for AXI_Master
// Bindable assertions and coverage focused on protocol, state/outputs coherence,
// transition correctness, and datapath integrity.

module AXI_Master_sva (
  input  logic         axi_clk,
  input  logic         axi_rst,

  input  logic [31:0]  axi_araddr,
  input  logic         axi_arvalid,
  input  logic         axi_arready,
  input  logic [31:0]  axi_rdata,
  input  logic         axi_rvalid,
  input  logic         axi_rready,

  input  logic [31:0]  axi_awaddr,
  input  logic         axi_awvalid,
  input  logic         axi_awready,
  input  logic [31:0]  axi_wdata,
  input  logic         axi_wvalid,
  input  logic         axi_wready,

  input  logic [1:0]   axi_bresp,
  input  logic         axi_bvalid,
  input  logic         axi_bready,

  // Internals
  input  logic [1:0]   state_reg,
  input  logic [31:0]  addr_reg,
  input  logic [31:0]  data_reg,
  input  logic [1:0]   resp_reg,
  input  logic [31:0]  mem [0:1023]
);

  // Encodings replicated to check legal state values
  localparam IDLE  = 2'b00;
  localparam READ  = 2'b01;
  localparam WRITE = 2'b10;

  default clocking cb @(posedge axi_clk); endclocking
  // Most properties disabled in reset; explicit reset checks provided separately.
  default disable iff (axi_rst);

  // ------------------------
  // Basic legal-state checks
  // ------------------------
  // No unknowns on key signals
  assert property (!$isunknown({state_reg, addr_reg, data_reg, resp_reg,
                                axi_arready, axi_awready, axi_wready,
                                axi_rvalid, axi_bvalid, axi_rdata, axi_bresp})))
    else $error("Unknown/X/Z detected on critical signals");

  // State encoding only in {IDLE, READ, WRITE}
  assert property (state_reg inside {IDLE, READ, WRITE})
    else $error("Illegal state encoding");

  // ------------------------
  // Output/state decode consistency
  // ------------------------
  // Ready signals identical and only in IDLE
  assert property (axi_arready == axi_awready && axi_arready == axi_wready)
    else $error("READY signals must match");
  assert property ((state_reg==IDLE) <-> axi_arready)
    else $error("READY decode vs state mismatch");

  // Valid decodes vs state
  assert property ((state_reg==READ)  <-> axi_rvalid)
    else $error("RVALID decode vs state mismatch");
  assert property ((state_reg==WRITE) <-> axi_bvalid)
    else $error("BVALID decode vs state mismatch");

  // Mutual exclusion of RVALID and BVALID; no READY high during valid
  assert property (!(axi_rvalid && axi_bvalid))
    else $error("RVALID and BVALID must not be high together");
  assert property (axi_rvalid |-> !(axi_arready || axi_awready || axi_wready))
    else $error("READY must be low while RVALID is high");
  assert property (axi_bvalid |-> !(axi_arready || axi_awready || axi_wready))
    else $error("READY must be low while BVALID is high");

  // ------------------------
  // Reset behavior (synchronous)
  // ------------------------
  property p_reset_sync;
    @(posedge axi_clk)
      axi_rst |=> (state_reg==IDLE && addr_reg==32'h0 && data_reg==32'h0 && resp_reg==2'b00
                   && axi_arready && !axi_rvalid && !axi_bvalid);
  endproperty
  assert property (p_reset_sync)
    else $error("Reset behavior mismatch");

  // ------------------------
  // Transaction entry/priority
  // ------------------------
  // Read entry from IDLE latches address and raises RVALID next cycle
  assert property ((state_reg==IDLE && axi_arvalid) |=> (axi_rvalid && addr_reg==$past(axi_araddr)))
    else $error("READ entry/addr latch failed");

  // Write entry from IDLE (no AR) latches AWADDR/WDATA and raises BVALID next cycle
  assert property ((state_reg==IDLE && axi_awvalid && !axi_arvalid)
                   |=> (axi_bvalid && addr_reg==$past(axi_awaddr) && data_reg==$past(axi_wdata)))
    else $error("WRITE entry/addr/data latch failed");

  // AR has priority over AW when both valid
  assert property ((state_reg==IDLE && axi_arvalid && axi_awvalid)
                   |=> (axi_rvalid && addr_reg==$past(axi_araddr) && $stable(data_reg)))
    else $error("AR priority over AW violated");

  // ------------------------
  // Sticky behavior under backpressure
  // ------------------------
  assert property (axi_rvalid && !axi_rready |=> axi_rvalid)
    else $error("RVALID must remain high until RREADY");
  assert property (axi_bvalid && !axi_bready |=> axi_bvalid)
    else $error("BVALID must remain high until BREADY");

  // Stay in READ/WRITE while not accepted; exit when accepted
  assert property ((state_reg==READ && !axi_rready)  |=> state_reg==READ)
    else $error("READ state must persist without RREADY");
  assert property ((state_reg==WRITE && !axi_bready) |=> state_reg==WRITE)
    else $error("WRITE state must persist without BREADY");

  assert property ((state_reg==READ  && axi_rready)  |=> (state_reg==IDLE && resp_reg==2'b00))
    else $error("READ completion transition/resp failed");
  assert property ((state_reg==WRITE && axi_bready)  |=> (state_reg==IDLE && resp_reg==2'b00))
    else $error("WRITE completion transition/resp failed");

  // ------------------------
  // Datapath correctness
  // ------------------------
  // rdata is memory at latched address in READ; zero otherwise
  assert property (axi_rvalid |-> (axi_rdata == mem[addr_reg]))
    else $error("RDATA mismatch vs mem at addr_reg");
  assert property (!axi_rvalid |-> (axi_rdata == 32'h0))
    else $error("RDATA must be zero when not in READ");

  // bresp equals resp_reg and is OKAY when valid
  assert property (axi_bresp == resp_reg)
    else $error("BRESP must mirror resp_reg");
  assert property (axi_bvalid |-> (axi_bresp == 2'b00))
    else $error("BRESP must be OKAY when BVALID");

  // Latched address/data stability while active
  assert property (axi_rvalid |-> $stable(addr_reg))
    else $error("addr_reg must be stable during READ");
  assert property (axi_bvalid |-> ($stable(addr_reg) && $stable(data_reg)))
    else $error("addr_reg/data_reg must be stable during WRITE");

  // ------------------------
  // Functional coverage
  // ------------------------
  // Read with delayed RREADY
  cover property ((state_reg==IDLE && axi_arvalid) ##1 axi_rvalid [*3] ##1 (axi_rvalid && axi_rready));

  // Write with delayed BREADY
  cover property ((state_reg==IDLE && axi_awvalid && !axi_arvalid) ##1 axi_bvalid [*2] ##1 (axi_bvalid && axi_bready));

  // AR priority over AW when both presented
  cover property ((state_reg==IDLE && axi_arvalid && axi_awvalid) ##1 axi_rvalid ##1 (axi_rvalid && axi_rready));

  // Back-to-back read then write
  cover property ((state_reg==IDLE && axi_arvalid) ##1 (axi_rvalid && axi_rready)
                  ##1 (state_reg==IDLE && axi_awvalid) ##1 (axi_bvalid && axi_bready));

  // Back-to-back write then read
  cover property ((state_reg==IDLE && axi_awvalid && !axi_arvalid) ##1 (axi_bvalid && axi_bready)
                  ##1 (state_reg==IDLE && axi_arvalid) ##1 (axi_rvalid && axi_rready));

endmodule

// Bind to DUT (connects internals to SVA)
bind AXI_Master AXI_Master_sva axi_master_sva_i (
  .axi_clk   (axi_clk),
  .axi_rst   (axi_rst),

  .axi_araddr(axi_araddr),
  .axi_arvalid(axi_arvalid),
  .axi_arready(axi_arready),
  .axi_rdata (axi_rdata),
  .axi_rvalid(axi_rvalid),
  .axi_rready(axi_rready),

  .axi_awaddr(axi_awaddr),
  .axi_awvalid(axi_awvalid),
  .axi_awready(axi_awready),
  .axi_wdata (axi_wdata),
  .axi_wvalid(axi_wvalid),
  .axi_wready(axi_wready),

  .axi_bresp (axi_bresp),
  .axi_bvalid(axi_bvalid),
  .axi_bready(axi_bready),

  .state_reg (state_reg),
  .addr_reg  (addr_reg),
  .data_reg  (data_reg),
  .resp_reg  (resp_reg),
  .mem       (mem)
);