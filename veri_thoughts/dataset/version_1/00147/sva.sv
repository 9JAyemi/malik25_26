// SVA checker for bin_to_decimal
module bin_to_decimal_sva (
  input logic        clk,
  input logic [15:0] B,
  input logic [19:0] bcdout
);

  function automatic logic valid_bcd (input logic [19:0] b);
    return (b[3:0]   <= 9) &&
           (b[7:4]   <= 9) &&
           (b[11:8]  <= 9) &&
           (b[15:12] <= 9) &&
           (b[19:16] <= 9);
  endfunction

  function automatic int unsigned bcd_to_int (input logic [19:0] b);
    int unsigned v;
    v  = b[3:0];
    v += 10    * b[7:4];
    v += 100   * b[11:8];
    v += 1000  * b[15:12];
    v += 10000 * b[19:16];
    return v;
  endfunction

  // No X/Z on inputs/outputs
  a_no_x_in:  assert property (@(posedge clk) !$isunknown(B));
  a_no_x_out: assert property (@(posedge clk) !$isunknown(bcdout));

  // BCD digit validity
  a_valid_bcd: assert property (@(posedge clk) valid_bcd(bcdout));

  // Functional correctness: BCD value equals binary input
  a_func: assert property (@(posedge clk) (!$isunknown(B) && !$isunknown(bcdout)) |-> (bcd_to_int(bcdout) == B));

  // Zero-latency combinational behavior (same-cycle after input change)
  a_zero_lat: assert property (@(posedge clk) $changed(B) |-> ##0 (bcd_to_int(bcdout) == B));

  // Stability: if input holds, output holds
  a_stable: assert property (@(posedge clk) $stable(B) |-> $stable(bcdout));

  // Corner-case coverage
  c_0:      cover property (@(posedge clk) B==16'd0     && bcd_to_int(bcdout)==0);
  c_9:      cover property (@(posedge clk) B==16'd9     && bcdout[3:0]==4'd9);
  c_10:     cover property (@(posedge clk) B==16'd10    && bcdout[7:0]==8'h10);
  c_15:     cover property (@(posedge clk) B==16'd15);
  c_99:     cover property (@(posedge clk) B==16'd99    && bcdout[7:0]==8'h99);
  c_100:    cover property (@(posedge clk) B==16'd100   && bcdout[11:0]==12'h100);
  c_999:    cover property (@(posedge clk) B==16'd999   && bcdout[11:0]==12'h999);
  c_9999:   cover property (@(posedge clk) B==16'd9999  && bcdout==20'h09999);
  c_max:    cover property (@(posedge clk) B==16'd65535);

  // Ensure each digit can reach 9 sometime
  c_ones9:   cover property (@(posedge clk) bcdout[3:0]==4'd9);
  c_tens9:   cover property (@(posedge clk) bcdout[7:4]==4'd9);
  c_hunds9:  cover property (@(posedge clk) bcdout[11:8]==4'd9);
  c_thous9:  cover property (@(posedge clk) bcdout[15:12]==4'd9);
  c_tthous9: cover property (@(posedge clk) bcdout[19:16]==4'd9);

endmodule

// Bind into DUT (provide a sampling clock from TB)
bind bin_to_decimal bin_to_decimal_sva u_bin_to_decimal_sva (.clk(clk), .B(B), .bcdout(bcdout));