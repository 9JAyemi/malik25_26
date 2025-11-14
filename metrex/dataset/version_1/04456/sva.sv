// SVA for bin_to_bcd_converter
// Focused, high-quality checks + concise full functional coverage

`ifndef BIN_TO_BCD_CONVERTER_SVA
`define BIN_TO_BCD_CONVERTER_SVA

module bin_to_bcd_converter_sva
(
  input logic        clk,
  input logic        rst,
  input logic [3:0]  bin_in,
  input logic [9:0]  bcd_out
);

  // Expected BCD encoder (2 MSBs zero, tens nibble, ones nibble)
  function automatic [9:0] exp_bcd (input logic [3:0] b);
    logic [3:0] tn, on;
    begin
      tn = (b >= 4'd10) ? 4'd1 : 4'd0;
      on = (b >= 4'd10) ? (b - 4'd10) : b;
      exp_bcd = {2'b00, tn, on};
    end
  endfunction

  // Async reset drives zero immediately and while asserted
  a_async_rst_now: assert property (@(posedge rst) bcd_out == 10'b0);
  a_rst_hold     : assert property (@(posedge clk) rst |-> bcd_out == 10'b0);

  // No X/Z on output post-reset
  a_known: assert property (@(posedge clk) disable iff (rst) !$isunknown(bcd_out));

  // Functional mapping: one-cycle latency from bin_in to bcd_out
  a_func: assert property (@(posedge clk) disable iff (rst)
                           $past(!rst) |-> (bcd_out == exp_bcd($past(bin_in))));

  // BCD shape/validity constraints
  a_shape: assert property (@(posedge clk) disable iff (rst)
    (bcd_out[9:8] == 2'b00) &&
    ((bcd_out[7:4] == 4'd0 && (bcd_out[3:0] inside {[4'd0:4'd9]})) ||
     (bcd_out[7:4] == 4'd1 && (bcd_out[3:0] inside {[4'd0:4'd5]})))
  );

  // Coverage: exercise all inputs and observe correct output next cycle
  genvar v;
  generate
    for (v = 0; v < 16; v++) begin : C
      c_bin2bcd: cover property (@(posedge clk) disable iff (rst)
        (bin_in == v[3:0]) ##1 (bcd_out == exp_bcd(v[3:0])));
    end
  endgenerate

  // Coverage: see both tens digits and a reset-to-conversion sequence
  c_tens0: cover property (@(posedge clk) disable iff (rst) bcd_out[7:4] == 4'd0);
  c_tens1: cover property (@(posedge clk) disable iff (rst) bcd_out[7:4] == 4'd1);
  c_reset_then_conv: cover property (@(posedge clk) $rose(rst) ##1 !rst ##1 $past(!rst) &&
                                     (bcd_out == exp_bcd($past(bin_in))));

endmodule

bind bin_to_bcd_converter bin_to_bcd_converter_sva sva_i (.*);

`endif