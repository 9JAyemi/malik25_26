// SVA for util_rfifo
// Bind into the DUT. Concise but checks all key behaviors and adds useful coverage.

module util_rfifo_sva #(
  parameter int DAC_DATA_WIDTH = 32,
  parameter int DMA_DATA_WIDTH = 64
)(
  input                           dac_clk,
  input                           dac_rd,
  input      [DAC_DATA_WIDTH-1:0] dac_rdata,
  input                           dac_runf,

  input                           dma_clk,
  input                           dma_rd,
  input      [DMA_DATA_WIDTH-1:0] dma_rdata,
  input                           dma_runf,

  input                           fifo_rst,
  input                           fifo_rstn,
  input                           fifo_wr,
  input      [DMA_DATA_WIDTH-1:0] fifo_wdata,
  input                           fifo_wfull,
  input                           fifo_rd,
  input      [DAC_DATA_WIDTH-1:0] fifo_rdata,
  input                           fifo_rempty,
  input                           fifo_runf
);

  // warm-up for $past
  logic past_dma, past_dac, past2_dac;
  always @(posedge dma_clk) past_dma <= 1'b1;
  always @(posedge dac_clk) begin
    past_dac  <= 1'b1;
    past2_dac <= past_dac;
  end

  // utility: bit-reverse
  function automatic [DMA_DATA_WIDTH-1:0] bitrev_dma(input [DMA_DATA_WIDTH-1:0] v);
    for (int i=0;i<DMA_DATA_WIDTH;i++) bitrev_dma[i]=v[DMA_DATA_WIDTH-1-i];
  endfunction
  function automatic [DAC_DATA_WIDTH-1:0] bitrev_dac(input [DAC_DATA_WIDTH-1:0] v);
    for (int i=0;i<DAC_DATA_WIDTH;i++) bitrev_dac[i]=v[DAC_DATA_WIDTH-1-i];
  endfunction

  // constants
  assert property (@(posedge dma_clk) fifo_rst  == 1'b0);
  assert property (@(posedge dma_clk) fifo_rstn == 1'b1);

  // dma side: registered backpressure and fifo_wr mirroring
  assert property (@(posedge dma_clk) past_dma |-> (dma_rd == $past(~fifo_wfull)));
  assert property (@(posedge dma_clk) fifo_wr == dma_rd);
  assert property (@(posedge dma_clk) past_dma |-> (fifo_wr == $past(~fifo_wfull)));
  assert property (@(posedge dma_clk) past_dma && $past(fifo_wfull) |-> !fifo_wr);

  // dac side: read enable formation
  assert property (@(posedge dac_clk) fifo_rd == (dac_rd & ~fifo_rempty));

  // data bit-reversal mappings
  assert property (@(posedge dma_clk) fifo_wdata == bitrev_dma(dma_rdata));
  assert property (@(posedge dac_clk) dac_rdata  == bitrev_dac(fifo_rdata));

  // runf synchronizer behavior under stable input
  // If (dma_runf|fifo_runf) stable for 3 dac_clk cycles, output equals value from 2 cycles earlier
  property p_runf_sync_stable;
    @(posedge dac_clk)
      past2_dac && ($stable(dma_runf | fifo_runf))[*3]
      |-> dac_runf == $past(dma_runf | fifo_runf, 2);
  endproperty
  assert property (p_runf_sync_stable);

  // known-ness on outputs (sampled on respective clocks)
  assert property (@(posedge dma_clk) !$isunknown({fifo_wr,fifo_wdata,fifo_rst,fifo_rstn,dma_rd}));
  assert property (@(posedge dac_clk) !$isunknown({fifo_rd,dac_rdata,dac_runf}));

  // Coverage
  cover property (@(posedge dma_clk) fifo_wr);
  cover property (@(posedge dac_clk) fifo_rd);
  cover property (@(posedge dma_clk) !fifo_wfull ##1 fifo_wfull ##1 !fifo_wfull);
  cover property (@(posedge dac_clk) (dma_runf|fifo_runf) ##2 dac_runf);

  // Bit-reversal extreme patterns
  localparam [DMA_DATA_WIDTH-1:0] DMA_LSB1 = {{(DMA_DATA_WIDTH-1){1'b0}},1'b1};
  localparam [DMA_DATA_WIDTH-1:0] DMA_MSB1 = {1'b1,{(DMA_DATA_WIDTH-1){1'b0}}};
  localparam [DAC_DATA_WIDTH-1:0] DAC_LSB1 = {{(DAC_DATA_WIDTH-1){1'b0}},1'b1};
  localparam [DAC_DATA_WIDTH-1:0] DAC_MSB1 = {1'b1,{(DAC_DATA_WIDTH-1){1'b0}}};

  cover property (@(posedge dma_clk) dma_rdata==DMA_LSB1 && fifo_wdata==DMA_MSB1);
  cover property (@(posedge dma_clk) dma_rdata==DMA_MSB1 && fifo_wdata==DMA_LSB1);
  cover property (@(posedge dac_clk) fifo_rdata==DAC_LSB1 && dac_rdata==DAC_MSB1);
  cover property (@(posedge dac_clk) fifo_rdata==DAC_MSB1 && dac_rdata==DAC_LSB1);

endmodule

bind util_rfifo util_rfifo_sva #(
  .DAC_DATA_WIDTH(DAC_DATA_WIDTH),
  .DMA_DATA_WIDTH(DMA_DATA_WIDTH)
) i_util_rfifo_sva (
  .dac_clk,
  .dac_rd,
  .dac_rdata,
  .dac_runf,
  .dma_clk,
  .dma_rd,
  .dma_rdata,
  .dma_runf,
  .fifo_rst,
  .fifo_rstn,
  .fifo_wr,
  .fifo_wdata,
  .fifo_wfull,
  .fifo_rd,
  .fifo_rdata,
  .fifo_rempty,
  .fifo_runf
);