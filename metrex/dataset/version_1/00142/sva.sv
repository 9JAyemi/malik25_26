// SVA for bit_capture_data
// Bind this module to the DUT:  bind bit_capture_data bit_capture_data_sva sva_inst(.*);

module bit_capture_data_sva (
  input  logic        posedge_clk,
  input  logic        negedge_clk,
  input  logic        rx_resetn,
  input  logic        rx_din,
  input  logic        bit_d_0,
  input  logic        bit_d_1,
  input  logic        bit_d_2,
  input  logic        bit_d_3,
  input  logic        bit_d_4,
  input  logic        bit_d_5,
  input  logic        bit_d_6,
  input  logic        bit_d_7,
  input  logic        bit_d_8,
  input  logic        bit_d_9
);

  // Reset values
  assert property (@(posedge posedge_clk) !rx_resetn |-> (bit_d_1==0 && bit_d_3==0 && bit_d_5==0 && bit_d_7==0 && bit_d_9==0));
  assert property (@(posedge negedge_clk) !rx_resetn |-> (bit_d_0==0 && bit_d_2==0 && bit_d_4==0 && bit_d_6==0 && bit_d_8==0));

  // Known (no X/Z) when out of reset
  assert property (@(posedge posedge_clk) rx_resetn |-> !$isunknown({bit_d_1,bit_d_3,bit_d_5,bit_d_7,bit_d_9}));
  assert property (@(posedge negedge_clk) rx_resetn |-> !$isunknown({bit_d_0,bit_d_2,bit_d_4,bit_d_6,bit_d_8}));

  // Odd pipeline (posedge_clk): pairwise stage-to-stage and first stage from input
  assert property (@(posedge posedge_clk) rx_resetn && $past(rx_resetn) |-> (
      bit_d_1 == $past(rx_din)  &&
      bit_d_3 == $past(bit_d_1) &&
      bit_d_5 == $past(bit_d_3) &&
      bit_d_7 == $past(bit_d_5) &&
      bit_d_9 == $past(bit_d_7)
  ));

  // Even pipeline (negedge_clk): pairwise stage-to-stage and first stage from input
  assert property (@(posedge negedge_clk) rx_resetn && $past(rx_resetn) |-> (
      bit_d_0 == $past(rx_din)  &&
      bit_d_2 == $past(bit_d_0) &&
      bit_d_4 == $past(bit_d_2) &&
      bit_d_6 == $past(bit_d_4) &&
      bit_d_8 == $past(bit_d_6)
  ));

  // End-to-end latency checks (robust, concise)
  assert property (@(posedge posedge_clk) rx_resetn && $past(rx_resetn,5) |-> bit_d_9 == $past(rx_din,5));
  assert property (@(posedge negedge_clk) rx_resetn && $past(rx_resetn,5) |-> bit_d_8 == $past(rx_din,5));

  // Stability on the opposite clock domain (no unintended updates)
  assert property (@(posedge negedge_clk) rx_resetn |-> $stable({bit_d_1,bit_d_3,bit_d_5,bit_d_7,bit_d_9}));
  assert property (@(posedge posedge_clk) rx_resetn |-> $stable({bit_d_0,bit_d_2,bit_d_4,bit_d_6,bit_d_8}));

  // Minimal functional coverage
  cover property (@(posedge posedge_clk) $rose(rx_resetn));
  cover property (@(posedge posedge_clk) rx_resetn && $changed(bit_d_9));
  cover property (@(posedge negedge_clk) rx_resetn && $changed(bit_d_8));
  cover property (@(posedge posedge_clk) rx_resetn && ($changed(bit_d_1) || $changed(bit_d_3) || $changed(bit_d_5) || $changed(bit_d_7) || $changed(bit_d_9)));
  cover property (@(posedge negedge_clk) rx_resetn && ($changed(bit_d_0) || $changed(bit_d_2) || $changed(bit_d_4) || $changed(bit_d_6) || $changed(bit_d_8)));

endmodule