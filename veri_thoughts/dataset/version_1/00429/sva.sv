// SVA for binary_counter: concise, high-quality checks and coverage

module binary_counter_sva #(parameter COUNTER_WIDTH=8)
(
  input logic                     clk,
  input logic                     rst,
  input logic [COUNTER_WIDTH-1:0] count
);

  default clocking cb @(posedge clk); endclocking

  // Track past-valid to safely use $past
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  localparam logic [COUNTER_WIDTH-1:0] MAX = {COUNTER_WIDTH{1'b1}};

  // Sanity: no X/Z on key signals
  a_no_x_rst:   assert property (! $isunknown(rst));
  a_no_x_count: assert property (! $isunknown(count));

  // Single functional next-state check (captures reset and increment w/ wrap)
  // count_next == (rst_prev ? 0 : count_prev + 1)
  a_functional: assert property ( disable iff (!past_valid)
                                  count == ( $past(rst) ? '0 : $past(count) + 1 ) );

  // Coverage: reset clears, normal increment, and wrap-around observed
  c_reset_clear: cover property ( $rose(rst) ##1 (count == '0) );
  c_increment:   cover property ( disable iff (!past_valid || rst)
                                  count == $past(count) + 1 );
  c_wrap:        cover property ( disable iff (!past_valid || rst)
                                  ($past(count) == MAX) && (count == '0) );

endmodule

// Bind to DUT
bind binary_counter
  binary_counter_sva #(.COUNTER_WIDTH(COUNTER_WIDTH))
  binary_counter_sva_i (.clk(clk), .rst(rst), .count(count));