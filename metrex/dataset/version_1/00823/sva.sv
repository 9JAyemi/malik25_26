// SVA for clk_rst_mngr
module clk_rst_mngr_sva (
  input  logic        clk_in,
  input  logic        rst_async_n,
  input  logic        en_clk_div8,
  input  logic        rst_sync_n,
  input  logic        clk_out,
  input  logic        clk_div2,
  input  logic        clk_div4,
  input  logic        clk_div8,
  input  logic        clk_div8_proc,
  input  logic [2:0]  counter,
  input  logic        synch_rst_reg1_n,
  input  logic        synch_rst_reg2_n,
  input  logic        en_clk_div8_reg
);

  // Basic sanity: clk_out mirrors clk_in
  assert property (@(posedge clk_in or negedge clk_in) clk_out == clk_in)
    else $error("clk_out must mirror clk_in");

  // Counter behavior (clk_in domain)
  assert property (@(posedge clk_in) !rst_async_n |-> counter == 3'b000)
    else $error("counter must be 0 while rst_async_n=0");

  assert property (@(posedge clk_in) rst_async_n && $past(rst_async_n) |-> counter == $past(counter)+3'd1)
    else $error("counter must increment when rst_async_n=1");

  // Divided clocks equal counter bits
  assert property (@(posedge clk_in) clk_div2 == counter[0] && clk_div4 == counter[1] && clk_div8 == counter[2])
    else $error("clk_div{2,4,8} must equal counter bits");

  // Optional: LSB toggles every clk_in when out of reset
  assert property (@(posedge clk_in) rst_async_n && $past(rst_async_n) |-> clk_div2 == ~$past(clk_div2))
    else $error("clk_div2 must toggle each clk_in when out of reset");

  // en_clk_div8_reg behavior (clk_div8 domain with async reset)
  assert property (@(negedge rst_async_n) en_clk_div8_reg == 1'b0)
    else $error("en_clk_div8_reg must async clear on rst_async_n low");

  assert property (@(posedge clk_div8) rst_async_n && $past(rst_async_n) |-> en_clk_div8_reg == $past(en_clk_div8))
    else $error("en_clk_div8_reg must capture en_clk_div8 on clk_div8");

  // Gated clock equation holds whenever any contributor can change
  assert property (@(posedge clk_in or posedge clk_div8 or negedge rst_async_n)
                   clk_div8_proc == ((en_clk_div8_reg && rst_async_n) ? counter[2] : 1'b0))
    else $error("clk_div8_proc must equal gate(en_clk_div8_reg & rst_async_n) of counter[2]");

  // Reset synchronizer internals (clk_div8 domain with async reset)
  assert property (@(negedge rst_async_n) !synch_rst_reg1_n && !synch_rst_reg2_n && !rst_sync_n)
    else $error("sync reset flops must async clear on rst_async_n low");

  assert property (@(posedge clk_div8) rst_async_n |-> (synch_rst_reg1_n == 1'b1 && synch_rst_reg2_n == $past(synch_rst_reg1_n)))
    else $error("sync reset flops must shift-in 1's on clk_div8 when rst_async_n=1");

  // rst_sync_n equals second stage
  assert property (@(posedge clk_div8 or negedge rst_async_n) rst_sync_n == synch_rst_reg2_n)
    else $error("rst_sync_n must equal synch_rst_reg2_n");

  // rst_sync_n deasserts 2 cycles after rst_async_n rise (clk_div8 domain)
  assert property (@(posedge clk_div8) $rose(rst_async_n) |-> (!rst_sync_n ##1 !rst_sync_n ##1 rst_sync_n))
    else $error("rst_sync_n must deassert 2 clk_div8 cycles after rst_async_n rises");

  // Once high, rst_sync_n stays high while rst_async_n stays high
  assert property (@(posedge clk_div8) rst_async_n && $past(rst_async_n) && $past(rst_sync_n) |-> rst_sync_n)
    else $error("rst_sync_n must remain high while rst_async_n is high");

  // Outputs should not be X/Z when sampled (basic hygiene)
  assert property (@(posedge clk_in) !$isunknown({clk_out, clk_div2, clk_div4, clk_div8}))
    else $error("clk_in-domain outputs contain X/Z");
  assert property (@(posedge clk_div8 or negedge rst_async_n) !$isunknown({rst_sync_n, clk_div8_proc}))
    else $error("clk_div8-domain outputs contain X/Z");

  // Coverage
  cover property (@(posedge clk_in) rst_async_n && $past(rst_async_n) && $past(counter)==3'b111 && counter==3'b000); // rollover
  cover property (@(posedge clk_div8) $rose(rst_async_n) ##2 rst_sync_n); // sync reset release
  cover property (@(posedge clk_div8) rst_async_n ##1 en_clk_div8_reg ##1 $changed(clk_div8_proc)); // gated clock toggles when enabled

endmodule

bind clk_rst_mngr clk_rst_mngr_sva i_clk_rst_mngr_sva (
  .clk_in(clk_in),
  .rst_async_n(rst_async_n),
  .en_clk_div8(en_clk_div8),
  .rst_sync_n(rst_sync_n),
  .clk_out(clk_out),
  .clk_div2(clk_div2),
  .clk_div4(clk_div4),
  .clk_div8(clk_div8),
  .clk_div8_proc(clk_div8_proc),
  .counter(counter),
  .synch_rst_reg1_n(synch_rst_reg1_n),
  .synch_rst_reg2_n(synch_rst_reg2_n),
  .en_clk_div8_reg(en_clk_div8_reg)
);