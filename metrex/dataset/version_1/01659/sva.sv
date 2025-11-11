// SVA for master
module master_sva #(
  parameter ADDR_WIDTH = 16,
  parameter IPL_READ_ADDR  = 16'h0,
  parameter IPL_WRITE_ADDR = 16'h1,
  parameter AW = ADDR_WIDTH - 1
)(
  input  logic                 clk_i,
  input  logic                 reset_i,

  // DUT inputs
  input  logic                 dreq_i,
  input  logic                 ack_i,

  // DUT outputs
  input  logic [AW:0]          adr_o,
  input  logic                 cyc_o,
  input  logic                 stb_o,
  input  logic                 we_o,
  input  logic                 dack_o,

  // DUT internals (bound)
  input  logic [AW:0]          rd_adr,
  input  logic [AW:0]          wr_adr,
  input  logic                 rd_cyc,
  input  logic                 wr_cyc
);

  // Reset behavior
  assert property (@(posedge clk_i) reset_i |=> (rd_adr==IPL_READ_ADDR && wr_adr==IPL_WRITE_ADDR
                                                 && !rd_cyc && !wr_cyc
                                                 && adr_o=='0 && !stb_o && !we_o && !dack_o));

  // Invariants/encoding
  assert property (@(posedge clk_i) disable iff (reset_i) cyc_o == (rd_cyc || wr_cyc));
  assert property (@(posedge clk_i) disable iff (reset_i) !(rd_cyc && wr_cyc));
  assert property (@(posedge clk_i) disable iff (reset_i) stb_o |-> cyc_o);
  assert property (@(posedge clk_i) disable iff (reset_i) we_o  |-> (stb_o && wr_cyc));
  assert property (@(posedge clk_i) disable iff (reset_i) rd_cyc |-> !we_o);
  assert property (@(posedge clk_i) disable iff (reset_i) !stb_o |-> (adr_o=='0));
  // Addresses are constant post-reset
  assert property (@(posedge clk_i) disable iff (reset_i) $stable(rd_adr) && $stable(wr_adr));

  // Legal state transitions
  // Start read when idle + dreq
  assert property (@(posedge clk_i) disable iff (reset_i)
    (dreq_i && !cyc_o) |=> (rd_cyc && stb_o && !we_o && dack_o && adr_o==rd_adr));

  // Read hold cycle (single-cycle strobe behavior)
  assert property (@(posedge clk_i) disable iff (reset_i)
    (rd_cyc && !ack_i) |-> (!stb_o && !we_o && !dack_o));
  assert property (@(posedge clk_i) disable iff (reset_i)
    (rd_cyc && !ack_i) |=> rd_cyc);

  // Read complete -> start write
  assert property (@(posedge clk_i) disable iff (reset_i)
    (rd_cyc && ack_i) |=> (!rd_cyc && wr_cyc && stb_o && we_o && adr_o==wr_adr));

  // Write hold cycle (single-cycle strobe behavior)
  assert property (@(posedge clk_i) disable iff (reset_i)
    (wr_cyc && !ack_i) |-> (!stb_o && !we_o && !dack_o));
  assert property (@(posedge clk_i) disable iff (reset_i)
    (wr_cyc && !ack_i) |=> wr_cyc);

  // Write complete -> either idle or immediate next read
  assert property (@(posedge clk_i) disable iff (reset_i)
    (wr_cyc && ack_i && !dreq_i) |=> (!wr_cyc && !rd_cyc && !stb_o && !we_o && !dack_o));
  assert property (@(posedge clk_i) disable iff (reset_i)
    (wr_cyc && ack_i &&  dreq_i) |=> ( rd_cyc && !wr_cyc && stb_o && !we_o && dack_o && adr_o==rd_adr));

  // Edges consistency
  assert property (@(posedge clk_i) disable iff (reset_i) $rose(rd_cyc) |-> $past(dreq_i));
  assert property (@(posedge clk_i) disable iff (reset_i) $rose(rd_cyc) |-> (stb_o && !we_o && dack_o && adr_o==rd_adr));
  assert property (@(posedge clk_i) disable iff (reset_i) $rose(wr_cyc) |-> $past(rd_cyc && ack_i));
  assert property (@(posedge clk_i) disable iff (reset_i) $rose(wr_cyc) |-> (stb_o && we_o && adr_o==wr_adr));
  assert property (@(posedge clk_i) disable iff (reset_i) $fell(rd_cyc) |-> $past(ack_i));
  assert property (@(posedge clk_i) disable iff (reset_i) $fell(wr_cyc) |-> $past(ack_i));

  // dack is only during read start
  assert property (@(posedge clk_i) disable iff (reset_i)
    dack_o |-> (stb_o && rd_cyc && !we_o && adr_o==rd_adr));

  // Robustness: spurious ack when idle does nothing (unless dreq starts read)
  assert property (@(posedge clk_i) disable iff (reset_i)
    (!cyc_o && ack_i && !dreq_i) |=> (!cyc_o && !stb_o && !we_o && !dack_o));

  // Coverage
  cover property (@(posedge clk_i) disable iff (reset_i)
    (!cyc_o && dreq_i)
    ##1 rd_cyc [*1:$] ##1 (rd_cyc && ack_i)
    ##1 (wr_cyc && stb_o && we_o)
    ##[1:$] (wr_cyc && ack_i)
    ##1 !cyc_o);

  cover property (@(posedge clk_i) disable iff (reset_i)
    (wr_cyc && ack_i && dreq_i) ##1 rd_cyc);

  cover property (@(posedge clk_i) disable iff (reset_i)
    (rd_cyc && !ack_i)[*2] ##1 (rd_cyc && ack_i));

  cover property (@(posedge clk_i) disable iff (reset_i)
    (wr_cyc && !ack_i)[*2] ##1 (wr_cyc && ack_i));

endmodule

// Example bind (inside a testbench or a package included after DUT)
// bind master master_sva #(.ADDR_WIDTH(ADDR_WIDTH), .IPL_READ_ADDR(IPL_READ_ADDR), .IPL_WRITE_ADDR(IPL_WRITE_ADDR))
//   u_master_sva ( .clk_i(clk_i), .reset_i(reset_i),
//                  .dreq_i(dreq_i), .ack_i(ack_i),
//                  .adr_o(adr_o), .cyc_o(cyc_o), .stb_o(stb_o), .we_o(we_o), .dack_o(dack_o),
//                  .rd_adr(rd_adr), .wr_adr(wr_adr), .rd_cyc(rd_cyc), .wr_cyc(wr_cyc) );