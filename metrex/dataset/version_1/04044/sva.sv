// SVA for ycbcr_to_rgb
// Bind into DUT; checks pipeline, math, saturation, and provides targeted coverage.

module ycbcr_to_rgb_sva;

  // Access DUT scope via bind; uses DUT's clk and internal regs/wires
  default clocking cb @(posedge clk); endclocking

  // Warmup to avoid $past hazards
  bit [2:0] warm_cnt; bit warm;
  always_ff @(posedge clk) warm_cnt <= warm_cnt + 3'd1;
  assign warm = (warm_cnt >= 3);
  default disable iff (!warm);

  // Helpers to mirror DUT arithmetic exactly
  function automatic signed [8:0] adj_from_y(input [7:0] y8);
    adj_from_y = $signed({1'b0, y8});
  endfunction

  // Implements 8-bit unsigned subtraction with wrap, then zero-extend to 9 and treat as signed
  function automatic signed [8:0] adj_from_cbcr(input [7:0] u8);
    adj_from_cbcr = $signed({1'b0, ((u8 - 8'd128) & 8'hff)});
  endfunction

  function automatic [7:0] clamp18_to_u8(input signed [17:0] x);
    if (x[17])        clamp18_to_u8 = 8'h00;
    else if (x[16] | x[15]) clamp18_to_u8 = 8'hff;
    else              clamp18_to_u8 = x[14:7];
  endfunction

  // Stage 1: adjust registers from inputs (with exact sizing/semantics)
  assert property (adj_y == $signed({1'b0, $past(y)}));
  assert property (adj_cb == $signed({1'b0, (($past(cb) - 8'd128) & 8'hff)}));
  assert property (adj_cr == $signed({1'b0, (($past(cr) - 8'd128) & 8'hff)}));

  // Stage 2: products (signed multiply)
  assert property (product_a == $signed($signed(const0) * $past(adj_y)));
  assert property (product_b == $signed($signed(const1) * $past(adj_cr)));
  assert property (product_c == $signed($signed(const2) * $past(adj_cr)));
  assert property (product_d == $signed($signed(const3) * $past(adj_cb)));
  assert property (product_e == $signed($signed(const4) * $past(adj_cb)));

  // Stage 3: sums (model truncation to 18 bits)
  assert property (sum_red   == $signed(( $past(product_a) + $past(product_b) ) [17:0]));
  assert property (sum_green == $signed(( $past(product_a) + $past(product_c) + $past(product_d) ) [17:0]));
  assert property (sum_blue  == $signed(( $past(product_a) + $past(product_e) ) [17:0]));

  // Stage 4: clamp/output
  assert property (red   == clamp18_to_u8($past(sum_red)));
  assert property (green == clamp18_to_u8($past(sum_green)));
  assert property (blue  == clamp18_to_u8($past(sum_blue)));

  // End-to-end 3-cycle checks from inputs to outputs (with exact truncation before clamp)
  assert property (red ==
    clamp18_to_u8( ( $signed(9'sd128)*adj_from_y($past(y,3))
                   + $signed(9'sd179)*adj_from_cbcr($past(cr,3)) ) [17:0] ));

  assert property (green ==
    clamp18_to_u8( ( $signed(9'sd128)*adj_from_y($past(y,3))
                   + $signed(-9'sd91)*adj_from_cbcr($past(cr,3))
                   + $signed(-9'sd44)*adj_from_cbcr($past(cb,3)) ) [17:0] ));

  assert property (blue ==
    clamp18_to_u8( ( $signed(9'sd128)*adj_from_y($past(y,3))
                   + $signed(9'sd227)*adj_from_cbcr($past(cb,3)) ) [17:0] ));

  // Basic sanity: no X/Z on outputs
  assert property (!$isunknown({red, green, blue}));

  // Coverage: hit each saturation mode per channel
  cover property ($past(sum_red)[17] && red == 8'h00);
  cover property ((!$past(sum_red)[17]) && ($past(sum_red)[16] || $past(sum_red)[15]) && red == 8'hff);
  cover property ((!$past(sum_red)[17]) && !($past(sum_red)[16] || $past(sum_red)[15]) && red == $past(sum_red[14:7]));

  cover property ($past(sum_green)[17] && green == 8'h00);
  cover property ((!$past(sum_green)[17]) && ($past(sum_green)[16] || $past(sum_green)[15]) && green == 8'hff);
  cover property ((!$past(sum_green)[17]) && !($past(sum_green)[16] || $past(sum_green)[15]) && green == $past(sum_green[14:7]));

  cover property ($past(sum_blue)[17] && blue == 8'h00);
  cover property ((!$past(sum_blue)[17]) && ($past(sum_blue)[16] || $past(sum_blue)[15]) && blue == 8'hff);
  cover property ((!$past(sum_blue)[17]) && !($past(sum_blue)[16] || $past(sum_blue)[15]) && blue == $past(sum_blue[14:7]));

endmodule

bind ycbcr_to_rgb ycbcr_to_rgb_sva sva();