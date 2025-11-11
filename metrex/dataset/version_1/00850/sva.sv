// SVA for binary_counter
module binary_counter_sva(
  input logic       clk,
  input logic       reset_n,
  input logic [3:0] count
);

  default clocking cb @(posedge clk); endclocking

  // Basic sanity
  assert property (@cb !$isunknown(reset_n));
  assert property (@cb disable iff (!reset_n) !$isunknown(count));

  // Async reset: immediate effect and hold while low
  assert property (@(negedge reset_n) ##0 (count == 4'd0));
  assert property (@cb !reset_n |-> (count == 4'd0));

  // Increment by 1 every cycle out of reset (implicit wrap in 4 bits)
  assert property (@cb disable iff (!reset_n) count == $past(count) + 4'd1);

  // Explicit wrap check for clarity
  assert property (@cb disable iff (!reset_n) ($past(count) == 4'hF) |-> (count == 4'h0));

  // First cycle after reset release should be 1
  assert property (@cb $rose(reset_n) |-> (count == 4'd1));

  // Coverage
  // - See each count value out of reset
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : cov_vals
      cover property (@cb disable iff (!reset_n) (count == i[3:0]));
    end
  endgenerate

  // - Observe wrap F->0 and a full 16-count cycle after release
  cover property (@cb disable iff (!reset_n) ($past(count) == 4'hF) && (count == 4'h0));
  cover property (@cb $rose(reset_n) ##1 (count == 4'd1) ##16 (count == 4'd1));

endmodule

// Bind into the DUT
bind binary_counter binary_counter_sva u_binary_counter_sva(.clk(clk), .reset_n(reset_n), .count(count));