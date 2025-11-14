// SVA checker for binary_counter
module binary_counter_sva #(parameter int WIDTH = 8)
(
  input logic                 clk,
  input logic                 reset,   // active-low async reset
  input logic [WIDTH-1:0]     count
);

  localparam logic [WIDTH-1:0] ZERO = '0;
  localparam logic [WIDTH-1:0] ONE  = {{(WIDTH-1){1'b0}},1'b1};
  localparam logic [WIDTH-1:0] ALL1 = {WIDTH{1'b1}};
  localparam logic [WIDTH-1:0] FE   = ALL1 - ONE;

  default clocking cb @(posedge clk); endclocking

  // Basic sanity/X checks
  assert property ( !$isunknown(reset) );                         // reset must be 0/1 at clk sample
  assert property ( reset |-> !$isunknown(count) );               // when reset=1, count must be known
  assert property ( !reset |-> (count == ZERO) );                 // while reset=0 at clk, count holds 0

  // Asynchronous clear on negedge reset (observe NBA update with ##0)
  assert property ( @(negedge reset) ##0 (count == ZERO) );

  // Increment by +1 on consecutive cycles with reset high (wrap handled by truncation)
  assert property ( (reset && $past(reset,1)) |-> (count == $past(count,1) + ONE) );

  // Explicit wrap check (FF -> 00) when reset high across adjacent cycles
  assert property ( (reset && $past(reset,1) && ($past(count,1) == ALL1)) |-> (count == ZERO) );

  // First value after reset release is 1 (previous clk saw reset=0, now =1)
  assert property ( $rose(reset) |-> (count == ONE) );

  // Coverage
  cover property ( $rose(reset) ##1 (count == ONE) );                          // post-release first count
  cover property ( (reset && $past(reset,2) && ($past(count,2)==FE) &&
                    ($past(count,1)==ALL1) && (count==ZERO) ) );               // FE -> FF -> 00 sequence
endmodule

// Bind to DUT
bind binary_counter binary_counter_sva #(.WIDTH(8)) u_binary_counter_sva (
  .clk   (clk),
  .reset (reset),
  .count (count)
);