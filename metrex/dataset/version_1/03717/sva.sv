// SVA for spi_shift
// Bind this file to the DUT. Focused, concise checks with key coverage.

module spi_shift_sva #(
  parameter int SPI_CHAR_LEN_BITS = 8,
  parameter int SPI_MAX_CHAR      = 18
)(
  input logic                       clk, rst, s_clk,
  input logic                       go, pos_edge, neg_edge,
  input logic                       rx_negedge, tx_negedge, lsb,
  input logic [17:0]                p_in,
  input logic [7:0]                 len,
  input logic                       tip, last,
  input logic [17:0]                p_out,
  input logic                       s_out,

  input logic [SPI_CHAR_LEN_BITS:0] cnt,
  input logic [SPI_MAX_CHAR-1:0]    data,
  input logic [SPI_CHAR_LEN_BITS:0] tx_bit_pos,
  input logic [SPI_CHAR_LEN_BITS:0] rx_bit_pos,
  input logic                       rx_clk, tx_clk
);

  // Common slices
  wire [SPI_CHAR_LEN_BITS-1:0] tx_idx = tx_bit_pos[SPI_CHAR_LEN_BITS-1:0];
  wire [SPI_CHAR_LEN_BITS-1:0] rx_idx = rx_bit_pos[SPI_CHAR_LEN_BITS-1:0];

  // -------------------------
  // Reset values (both clocks)
  // -------------------------
  assert property (@(posedge clk) rst |-> (cnt == '0 && tip == 1'b0 && s_out == 1'b0 && last == 1'b0))
    else $error("RST clamp failed on clk domain");

  assert property (@(posedge s_clk) rst |-> (data == '0 && p_out == '0))
    else $error("RST clamp failed on s_clk domain");

  // -------------------------
  // Counter behavior
  // -------------------------
  // Load when !tip
  assert property (@(posedge clk) disable iff (rst)
                   (!tip) |-> (cnt == ((len == '0) ? {1'b1, {SPI_CHAR_LEN_BITS{1'b0}}}
                                                  : {1'b0, len})))
    else $error("CNT load mismatch");

  // Decrement on pos_edge when tip
  assert property (@(posedge clk) disable iff (rst)
                   (tip && pos_edge) |=> (cnt == $past(cnt) - {{SPI_CHAR_LEN_BITS{1'b0}},1'b1}))
    else $error("CNT decrement mismatch");

  // Hold when no pos_edge and tip
  assert property (@(posedge clk) disable iff (rst)
                   (tip && !pos_edge) |=> (cnt == $past(cnt)))
    else $error("CNT hold mismatch");

  // last is registered zero-detect of previous cnt
  assert property (@(posedge clk) disable iff (rst)
                   1 |-> (last == !(|$past(cnt))))
    else $error("last misaligned to previous cnt");

  // -------------------------
  // TIP handshake
  // -------------------------
  // Set on go when idle
  assert property (@(posedge clk) disable iff (rst)
                   (go && !tip) |=> tip)
    else $error("TIP not set by GO");

  // TIP rising edge implies past GO while idle
  assert property (@(posedge clk) disable iff (rst)
                   $rose(tip) |-> $past(go && !$past(tip)))
    else $error("Unexpected TIP rise");

  // Clear on last & pos_edge
  assert property (@(posedge clk) disable iff (rst)
                   (tip && last && pos_edge) |=> !tip)
    else $error("TIP not cleared on last & pos_edge");

  // Stay set otherwise
  assert property (@(posedge clk) disable iff (rst)
                   (tip && !(last && pos_edge)) |=> tip)
    else $error("TIP dropped early");

  // -------------------------
  // s_out update protocol (clk domain)
  // -------------------------
  // Hold when active and no tx_clk
  assert property (@(posedge clk) disable iff (rst)
                   (tip && !tx_clk) |=> $stable(s_out))
    else $error("s_out changed without tx_clk when active");

  // Update on tx_clk or when idle; value equals selected data bit
  assert property (@(posedge clk) disable iff (rst)
                   (tx_clk || !tip) |=> (s_out == $past(data[$past(tx_idx)])))
    else $error("s_out update value mismatch");

  // -------------------------
  // Shift register (s_clk domain)
  // -------------------------
  assert property (@(posedge s_clk) disable iff (rst)
                   1 |=> (data == { $past(data[SPI_MAX_CHAR-2:0]), $past(p_in) }))
    else $error("DATA shift mismatch");

  // p_out follows previous data[17:0] with a 0 LSB (s_clk domain)
  assert property (@(posedge s_clk) disable iff (rst)
                   1 |=> (p_out == { $past(data[17:0]), 1'b0 }))
    else $error("p_out update mismatch");

  // -------------------------
  // Index/range safety
  // -------------------------
  // Prevent out-of-range indexing of data when s_out samples
  assert property (@(posedge clk) disable iff (rst)
                   (tx_clk || !tip) |-> (tx_idx < SPI_MAX_CHAR))
    else $error("tx_idx out of range");

  // If/when rx sampling used, ensure index is in range on rx_clk
  assert property (@(posedge clk) disable iff (rst)
                   rx_clk |-> (rx_idx < SPI_MAX_CHAR))
    else $error("rx_idx out of range");

  // No tx_clk allowed on last
  assert property (@(posedge clk) disable iff (rst)
                   last |-> !tx_clk)
    else $error("tx_clk asserted while last");

  // -------------------------
  // Key covers
  // -------------------------
  // Start-to-finish transaction
  cover property (@(posedge clk) disable iff (rst)
                  $rose(tip) ##[1:$] (last && pos_edge) ##1 !tip);

  // Cover both bit orders
  cover property (@(posedge clk) disable iff (rst) $rose(tip) && (lsb == 1'b0));
  cover property (@(posedge clk) disable iff (rst) $rose(tip) && (lsb == 1'b1));

  // Cover both TX edge polarities
  cover property (@(posedge clk) disable iff (rst) $rose(tip) && (tx_negedge == 1'b0));
  cover property (@(posedge clk) disable iff (rst) $rose(tip) && (tx_negedge == 1'b1));

  // Cover both RX edge polarities and last gating with s_clk
  cover property (@(posedge clk) disable iff (rst)
                  last && s_clk && (rx_negedge ? neg_edge : pos_edge) ##1 rx_clk);

  // Zero-length transfer mode seen
  cover property (@(posedge clk) disable iff (rst) $rose(tip) && (len == 8'd0));

endmodule

// Bind into DUT (parameters use DUT defaults 8/18)
bind spi_shift spi_shift_sva #(.SPI_CHAR_LEN_BITS(8), .SPI_MAX_CHAR(18)) spi_shift_sva_b (
  .clk(clk), .rst(rst), .s_clk(s_clk),
  .go(go), .pos_edge(pos_edge), .neg_edge(neg_edge),
  .rx_negedge(rx_negedge), .tx_negedge(tx_negedge), .lsb(lsb),
  .p_in(p_in), .len(len),
  .tip(tip), .last(last), .p_out(p_out), .s_out(s_out),
  .cnt(cnt), .data(data),
  .tx_bit_pos(tx_bit_pos), .rx_bit_pos(rx_bit_pos),
  .rx_clk(rx_clk), .tx_clk(tx_clk)
);