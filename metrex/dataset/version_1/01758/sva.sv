// SVA for up_counter: concise, high-quality checks and coverage
module up_counter_sva (
  input logic        clk,
  input logic        reset,   // active-low in DUT; here treat 1=not in reset
  input logic [3:0]  out
);
  // Clocking on DUT clk posedge
  default clocking cb @(posedge clk); endclocking

  // 1) Asynchronous reset must drive out to 0 immediately (after NBA)
  assert property (@(negedge reset) ##0 (out == 4'd0))
    else $error("out not 0 immediately on async reset assert");

  // 2) While reset is low, out must be 0 on every clk edge
  assert property ( !reset |-> (out == 4'd0) )
    else $error("out not 0 while reset is low");

  // 3) When reset is high on consecutive clocks, counter increments by 1 (mod 16)
  assert property ( reset && $past(reset) |-> (out == $past(out) + 4'd1) )
    else $error("out failed +1 increment on consecutive enabled clocks");

  // 4) First enabled tick after reset deassertion must produce 1 (since out was 0)
  assert property ( $rose(reset) |-> (out == 4'd1) )
    else $error("out not 1 on first clock after reset deassert");

  // 5) No X/Z on key signals at clock sample
  assert property ( !$isunknown(reset) )
    else $error("reset is X/Z at clk edge");
  assert property ( !$isunknown(out) )
    else $error("out is X/Z at clk edge");

  // Coverage

  // C1) Observe wrap-around from 15 -> 0 under enabled counting
  cover property ( reset && $past(reset) && ($past(out) == 4'hF) && (out == 4'h0) );

  // C2) Observe release then first increment to 1
  cover property ( $rose(reset) && (out == 4'd1) );

  // C3) Observe a normal increment (e.g., 7 -> 8) under enabled counting
  cover property ( reset && $past(reset) && ($past(out) == 4'd7) && (out == 4'd8) );
endmodule

// Bind into DUT
bind up_counter up_counter_sva sva_i (.clk(clk), .reset(reset), .out(out));