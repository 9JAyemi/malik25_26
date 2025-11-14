// SVA for counter. Bind this to the DUT.
module counter_sva(
  input logic        clk,
  input logic        rst,
  input logic        en,
  input logic [15:0] max_count,
  input logic [15:0] count
);

  default clocking cb @ (posedge clk); endclocking

  logic past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;
  default disable iff (!past_valid);

  // Reset behavior: synchronous clear
  assert property (rst |=> count == 16'd0);

  // Hold when disabled (no reset)
  assert property ($past(!rst && !en) |-> count == $past(count));

  // Enabled behavior (based on previous cycle values): increment or wrap to 0
  assert property (
    $past(!rst && en) |->
      ( ($past(count == max_count) && count == 16'd0) ||
        ($past(count != max_count) && count == $past(count) + 16'd1) )
  );

  // Coverage
  cover property ($past(!rst && en && (count != max_count)) && count == $past(count) + 16'd1); // increment
  cover property ($past(!rst && en && (count == max_count)) && count == 16'd0);                // wrap
  cover property ($past(!rst && !en) && count == $past(count));                                 // hold
  cover property (rst);                                                                         // reset seen
  cover property ($past(!rst && en && (max_count == 16'd0)) && count == 16'd0);                 // degenerate max=0
endmodule

bind counter counter_sva sva (
  .clk(clk),
  .rst(rst),
  .en(en),
  .max_count(max_count),
  .count(count)
);