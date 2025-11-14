// Drop inside the module or bind to it. Concise SVA focusing on protocol, gating, arbitration, pass-through, and coverage.
`ifndef SYNTHESIS
// Assertions use internal state; keep in-module or bind into scope where these are visible.
default clocking cb @(posedge ACLK); endclocking
default disable iff (|areset_d)

// Arbitration and state
assert property(!(read_req && write_req));
assert property(!(read_active && write_active));
assert property(busy |-> (!read_req && !write_req));
assert property((read_req && M_AXI_ARREADY) |-> ##1 busy);
assert property((write_req && M_AXI_AWREADY) |-> ##1 busy);
assert property(busy && !(read_complete || write_complete) |=> busy);

assert property(read_req |-> ##1 read_active);
assert property(write_req |-> ##1 write_active);
assert property(read_active && !read_complete |=> read_active);
assert property(write_active && !write_complete |=> write_active);

// Handshake mapping
assert property(M_AXI_ARVALID == read_req);
assert property(S_AXI_ARREADY == (M_AXI_ARREADY & read_req));
assert property(M_AXI_AWVALID == write_req);
assert property(S_AXI_AWREADY == (M_AXI_AWREADY & write_req));

// R/B channel gating
assert property(S_AXI_RVALID == (M_AXI_RVALID & read_active));
assert property(M_AXI_RREADY == (S_AXI_RREADY & read_active));
assert property(S_AXI_BVALID == (M_AXI_BVALID & write_active));
assert property(M_AXI_BREADY == (S_AXI_BREADY & write_active));

// Pass-through and AXI-Lite semantics
assert property(S_AXI_RDATA == M_AXI_RDATA);
assert property(S_AXI_RRESP == M_AXI_RRESP);
assert property(S_AXI_BRESP == M_AXI_BRESP);
assert property(M_AXI_WVALID == (S_AXI_WVALID & ~|areset_d));
assert property(S_AXI_WREADY == (M_AXI_WREADY & ~|areset_d));
assert property(M_AXI_WDATA == S_AXI_WDATA);
assert property(M_AXI_WSTRB == S_AXI_WSTRB);
assert property(M_AXI_AWPROT == S_AXI_AWPROT);
assert property(M_AXI_ARPROT == S_AXI_ARPROT);
assert property(S_AXI_RVALID |-> S_AXI_RLAST);

// Address mux behavior (both outputs always equal selected addr)
assert property(M_AXI_ARADDR == M_AXI_AWADDR);

generate
  if (C_AXI_SUPPORTS_WRITE == 0) begin : g_nowrite
    assert property(!M_AXI_AWVALID && !S_AXI_AWREADY && !write_req && !write_active);
    assert property(M_AXI_ARADDR == S_AXI_ARADDR && M_AXI_AWADDR == S_AXI_ARADDR);
  end else begin : g_write
    assert property(read_req |-> (M_AXI_ARADDR == S_AXI_ARADDR));
    assert property(!read_req |-> (M_AXI_AWADDR == S_AXI_AWADDR));
  end
  if (C_AXI_SUPPORTS_READ == 0) begin : g_noread
    assert property(!M_AXI_ARVALID && !S_AXI_ARREADY && !read_req && !read_active);
    assert property(!S_AXI_RVALID && !M_AXI_RREADY);
  end
endgenerate

// ID capture/hold
property rid_holds;
  logic [C_AXI_ID_WIDTH-1:0] cap;
  (read_req && !read_active, cap = S_AXI_ARID) ##1 read_active |-> (read_active throughout (S_AXI_RID == cap));
endproperty
assert property(rid_holds);

property bid_holds;
  logic [C_AXI_ID_WIDTH-1:0] cap;
  (write_req && !write_active, cap = S_AXI_AWID) ##1 write_active |-> (write_active throughout (S_AXI_BID == cap));
endproperty
assert property(bid_holds);

// Minimal upstream stability (AXI-lite)
assert property(S_AXI_ARVALID && !S_AXI_ARREADY |=> $stable(S_AXI_ARADDR) && $stable(S_AXI_ARPROT) && $stable(S_AXI_ARID));
if (C_AXI_SUPPORTS_WRITE != 0) begin
  assert property(S_AXI_AWVALID && !S_AXI_AWREADY |=> $stable(S_AXI_AWADDR) && $stable(S_AXI_AWPROT) && $stable(S_AXI_AWID));
  assert property(S_AXI_WVALID  && !S_AXI_WREADY  |=> $stable(S_AXI_WDATA)  && $stable(S_AXI_WSTRB));
end

// Coverage
cover property(!|areset_d && C_AXI_SUPPORTS_READ  && S_AXI_ARVALID && M_AXI_ARREADY);
cover property(!|areset_d && C_AXI_SUPPORTS_WRITE && S_AXI_AWVALID && M_AXI_AWREADY && S_AXI_WVALID && M_AXI_WREADY);
// Read vs write contention: read priority
cover property(!|areset_d && C_AXI_SUPPORTS_READ && C_AXI_SUPPORTS_WRITE &&
               S_AXI_ARVALID && S_AXI_AWVALID && !busy && !read_active && !write_active ##1 read_req && !write_req);
// Back-to-back read then write completions
cover property(read_req ##[1:$] read_complete ##1 write_req ##[1:$] write_complete);
`endif