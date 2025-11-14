// SVA for led_blink
module led_blink_sva #(
  parameter int BLINK_ON_CLKS  = 1024,
  parameter int BLINK_OFF_CLKS = 1024
)(
  input  logic        clk,
  input  logic        n_reset,
  input  logic        enable,
  input  logic        led,
  input  logic [31:0] led_on_count,
  input  logic [31:0] led_off_count
);

  default clocking cb @(posedge clk); endclocking
  localparam int ON_LEN  = BLINK_ON_CLKS  + 1;
  localparam int OFF_LEN = BLINK_OFF_CLKS + 1;

  // Synchronous active-low reset drives zeros
  assert property (@(posedge clk) !n_reset |=> (led==0 && led_on_count==0 && led_off_count==0));

  // All other checks disabled during reset
  default disable iff (!n_reset)

  // Invariants tying LED state to counters
  assert property ( led  |-> (led_off_count==0) );
  assert property (!led  |-> (led_on_count==0) );
  assert property (led_on_count  <= BLINK_ON_CLKS);
  assert property (led_off_count <= BLINK_OFF_CLKS);

  // Monotonic decrement when active
  assert property ( led && (led_on_count>0)  |=>  led && (led_on_count == $past(led_on_count)-1) && (led_off_count == $past(led_off_count)) );
  assert property (!led && (led_off_count>0) |=> !led && (led_off_count == $past(led_off_count)-1) && (led_on_count  == $past(led_on_count )) );

  // Transition causes and loads
  assert property ( $fell(led) |-> (led_off_count == BLINK_OFF_CLKS) && $past(led_on_count==0) );
  assert property ( $rose(led) |-> (led_on_count  == BLINK_ON_CLKS)  && $past(led_off_count==0 && enable) );

  // Immediate next-state effects when counters hit zero
  assert property (  led && (led_on_count==0)          |=> !led );
  assert property ( !led && (led_off_count==0) && enable |=>  $rose(led) );

  // Exact ON duration, minimum OFF duration
  assert property ( $rose(led) |-> led[*ON_LEN] ##1 $fell(led) );
  assert property ( $fell(led) |-> !led[*OFF_LEN] );

  // Functional coverage
  cover property ( $rose(led) );
  cover property ( $fell(led) );
  // Full period with enable high
  cover property ( $fell(led) ##OFF_LEN $rose(led) ##ON_LEN $fell(led) );
  // Off stall due to enable low, then rise when re-enabled
  cover property ( (!led && (led_off_count==0) && !enable)
                   ##1 (!led && (led_off_count==0) && enable)
                   ##1 $rose(led) );

endmodule

bind led_blink led_blink_sva #(
  .BLINK_ON_CLKS (BLINK_ON_CLKS),
  .BLINK_OFF_CLKS(BLINK_OFF_CLKS)
) led_blink_sva_i (
  .clk(clk),
  .n_reset(n_reset),
  .enable(enable),
  .led(led),
  .led_on_count(led_on_count),
  .led_off_count(led_off_count)
);