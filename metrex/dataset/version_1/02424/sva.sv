// SVA for priority_encoder
// Bind this module to the DUT instance.
module priority_encoder_sva (input logic clk, rst,
                             input logic [3:0] in,
                             input logic [1:0] out);

  // Basic sanity
  ap_out_known:        assert property (@(posedge clk) !$isunknown(out));

  // Asynchronous reset behavior
  ap_rst_async_set:    assert property (@(posedge rst) out == 2'b00);
  ap_rst_hold:         assert property (@(posedge clk) rst |-> (out == 2'b00));

  // Functional encoding on clock (when not in reset)
  ap_enc_0001:         assert property (@(posedge clk) disable iff (rst) (in == 4'b0001) |-> (out == 2'b00));
  ap_enc_0010:         assert property (@(posedge clk) disable iff (rst) (in == 4'b0010) |-> (out == 2'b01));
  ap_enc_0100:         assert property (@(posedge clk) disable iff (rst) (in == 4'b0100) |-> (out == 2'b10));
  ap_enc_1000:         assert property (@(posedge clk) disable iff (rst) (in == 4'b1000) |-> (out == 2'b11));

  // Default branch for all non-onehot known inputs (includes 4'b0000 and multi-hot)
  ap_default_else:     assert property (@(posedge clk) disable iff (rst)
                                        (!$isunknown(in) && !$onehot(in)) |-> (out == 2'b00));

  // Coverage: hit all mappings, default via zero and multi-hot, and reset events
  cp_enc_0001:         cover property (@(posedge clk) disable iff (rst) (in == 4'b0001) && (out == 2'b00));
  cp_enc_0010:         cover property (@(posedge clk) disable iff (rst) (in == 4'b0010) && (out == 2'b01));
  cp_enc_0100:         cover property (@(posedge clk) disable iff (rst) (in == 4'b0100) && (out == 2'b10));
  cp_enc_1000:         cover property (@(posedge clk) disable iff (rst) (in == 4'b1000) && (out == 2'b11));
  cp_default_zero:     cover property (@(posedge clk) disable iff (rst) (in == 4'b0000) && (out == 2'b00));
  cp_default_multi:    cover property (@(posedge clk) disable iff (rst)
                                        (!$isunknown(in) && ($countones(in) >= 2)) && (out == 2'b00));
  cp_rst_assert:       cover property (@(posedge rst) 1);
  cp_rst_release_then_decode:
                       cover property (@(posedge clk) $fell(rst) ##1 $onehot(in));

endmodule

// Bind to DUT (adjust instance path if needed)
bind priority_encoder priority_encoder_sva i_priority_encoder_sva(.clk(clk), .rst(rst), .in(in), .out(out));