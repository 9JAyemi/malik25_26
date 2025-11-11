// SVA for openhmc_ram
// Bind into DUT; references internal signals for precise checking

module openhmc_ram_sva #(
  parameter DATASIZE  = 78,
  parameter ADDRSIZE  = 9,
  parameter PIPELINED = 0
) ();

  default clocking cb @(posedge clk); endclocking

  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // Always true by design wiring
  assert property (rdata_ram == data_out);

  // Memory write takes effect next cycle
  property p_write_effect;
    automatic logic [ADDRSIZE-1:0] a;
    automatic logic [DATASIZE-1:0] d;
    disable iff (!past_valid)
    wen ##0 (a = waddr, d = wdata) |-> ##1 (MEM[a] == d);
  endproperty
  assert property (p_write_effect);

  // data_out only updates on ren
  assert property (disable iff (!past_valid) !ren |-> (data_out == $past(data_out)));

  // Read data latency and gating
  if (PIPELINED == 0) begin : gen_np
    // rdata is directly from data_out
    assert property (rdata == rdata_ram);

    // On ren, capture address and pre-write MEM value; rdata/data_out reflect it next cycle (Observed region)
    property p_read_np;
      automatic logic [ADDRSIZE-1:0] a;
      automatic logic [DATASIZE-1:0] v;
      disable iff (!past_valid)
      ren ##0 (a = raddr, v = MEM[a]) |-> ##1 (rdata == v && data_out == v);
    endproperty
    assert property (p_read_np);

    // rdata holds when ren is low
    assert property (disable iff (!past_valid) !ren |-> (rdata == $past(rdata)));
  end else begin : gen_pipe
    // Pipeline internal relations
    assert property (disable iff (!past_valid) ren_dly == $past(ren));
    assert property (rdata == rdata_dly);
    assert property (disable iff (!past_valid) !ren_dly |-> (rdata_dly == $past(rdata_dly)));

    // On ren, capture address and pre-write MEM value; rdata reflects it after 2 cycles (Observed region)
    property p_read_pipe;
      automatic logic [ADDRSIZE-1:0] a;
      automatic logic [DATASIZE-1:0] v;
      disable iff (!past_valid)
      ren ##0 (a = raddr, v = MEM[a]) |-> ##2 (rdata == v);
    endproperty
    assert property (p_read_pipe);

    // rdata updates only when previous cycle had ren
    assert property (disable iff (!past_valid) !$past(ren) |-> (rdata == $past(rdata)));
  end

  // Basic X-checks on controls when used
  assert property (disable iff (!past_valid) wen |-> (!$isunknown(waddr) && !$isunknown(wdata)));
  assert property (disable iff (!past_valid) ren |-> (!$isunknown(raddr)));

  // Coverage: concurrent read/write same address (old data should be returned per read assertions)
  cover property (ren && wen && (raddr == waddr));

  // Coverage: back-to-back reads to different addresses
  cover property (ren ##1 (ren && (raddr != $past(raddr))));

  // Coverage: write then read same address
  cover property (wen ##1 (ren && (raddr == $past(waddr))));
endmodule

bind openhmc_ram openhmc_ram_sva #(
  .DATASIZE(DATASIZE),
  .ADDRSIZE(ADDRSIZE),
  .PIPELINED(PIPELINED)
) ();