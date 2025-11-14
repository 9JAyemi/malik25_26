// SVA checker for cur_ram_blk
module cur_ram_blk_sva (
  input  logic        hclk,
  input  logic        pixclk,
  input  logic        write,
  input  logic [8:0]  cpu_address,
  input  logic [7:0]  cpu_data_in,
  input  logic [8:0]  cur_address,
  input  logic [7:0]  cur_data_out,
  input  logic [7:0]  cpu_data_out,
  ref    logic [7:0]  ram_data [0:511]
);

  // past-valid per clock
  logic pv_h, pv_p;
  initial begin pv_h = 1'b0; pv_p = 1'b0; end
  always @(posedge hclk)   pv_h <= 1'b1;
  always @(posedge pixclk) pv_p <= 1'b1;

  // Basic sanity (no X on key controls/addr when sampled)
  assert property (@(posedge hclk)   !$isunknown({write,cpu_address,cpu_data_in}));
  assert property (@(posedge pixclk) !$isunknown({write,cur_address}));

  // CPU read port must mirror memory (sampled on both clocks)
  assert property (@(posedge hclk or posedge pixclk) cpu_data_out == ram_data[cpu_address]);

  // Synchronous write updates memory at next hclk
  assert property (@(posedge hclk) disable iff (!pv_h)
                   write |=> ram_data[$past(cpu_address)] == $past(cpu_data_in));

  // When not writing, the last-addressed location holds across hclk edges
  assert property (@(posedge hclk) disable iff (!pv_h)
                   !write |=> ram_data[$past(cpu_address)] == $past(ram_data[$past(cpu_address)]));

  // Pixel-domain read: update when !write, hold when write
  assert property (@(posedge pixclk) disable iff (!pv_p)
                   !write |=> cur_data_out == $past(ram_data[$past(cur_address)]));
  assert property (@(posedge pixclk) disable iff (!pv_p)
                   write  |=> cur_data_out == $past(cur_data_out));

  // After an enabled read, output must be known
  assert property (@(posedge pixclk) disable iff (!pv_p)
                   !write |=> !$isunknown(cur_data_out));

  // Coverage: boundary addresses, data extremes, gating, back-to-back writes
  cover property (@(posedge hclk)   write && cpu_address==9'd0);
  cover property (@(posedge hclk)   write && cpu_address==9'd511);
  cover property (@(posedge hclk)   write && (cpu_data_in==8'h00));
  cover property (@(posedge hclk)   write && (cpu_data_in==8'hFF));
  cover property (@(posedge hclk)   write ##1 write);
  cover property (@(posedge pixclk) !write && cur_address==9'd0);
  cover property (@(posedge pixclk) !write && cur_address==9'd511);
  cover property (@(posedge pixclk) write);

  // Cross-domain functional cover: write then later readback of same address/value
  property c_write_then_readback;
    logic [8:0] a; logic [7:0] d;
    @(posedge hclk)
      (write, a = cpu_address, d = cpu_data_in)
      ##1
      ##[0:$] @(posedge pixclk) (!write && cur_address == a)
      ##1      @(posedge pixclk) cur_data_out == d;
  endproperty
  cover property (c_write_then_readback);

endmodule

// Bind into DUT
bind cur_ram_blk cur_ram_blk_sva i_cur_ram_blk_sva (
  .hclk(hclk),
  .pixclk(pixclk),
  .write(write),
  .cpu_address(cpu_address),
  .cpu_data_in(cpu_data_in),
  .cur_address(cur_address),
  .cur_data_out(cur_data_out),
  .cpu_data_out(cpu_data_out),
  .ram_data(ram_data)
);