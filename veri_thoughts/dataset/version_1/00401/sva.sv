// SVA for counter: concise, full functional checks and coverage
module counter_sva #(parameter WIDTH=8)
(
  input rstn,
  input clk,
  input up,
  input down,
  input [WIDTH-1:0] count
);
  localparam [WIDTH-1:0] MAX = {WIDTH{1'b1}};

  // No X on key signals during operation
  assert property (@(posedge clk) rstn |-> !$isunknown({up, down, count}));

  // Async reset: immediate and held at 0
  assert property (@(negedge rstn) count == '0);
  assert property (@(posedge clk) !rstn |-> count == '0);

  // Increment, decrement, and hold behaviors
  assert property (@(posedge clk) disable iff (!rstn)
                   ($past(rstn) &&  up && !down) |=> count == $past(count) + 1);
  assert property (@(posedge clk) disable iff (!rstn)
                   ($past(rstn) && !up &&  down) |=> count == $past(count) - 1);
  assert property (@(posedge clk) disable iff (!rstn)
                   ($past(rstn) && !(up ^ down)) |=> count == $past(count));

  // No unexpected state changes
  assert property (@(posedge clk) disable iff (!rstn)
                   ($past(rstn) && (count != $past(count))) |-> (up ^ down));

  // Coverage: basic ops
  cover  property (@(posedge clk) disable iff (!rstn)
                   $past(rstn) &&  up && !down |=> count == $past(count) + 1);
  cover  property (@(posedge clk) disable iff (!rstn)
                   $past(rstn) && !up &&  down |=> count == $past(count) - 1);
  cover  property (@(posedge clk) disable iff (!rstn)
                   $past(rstn) && (up && down) |=> count == $past(count));
  cover  property (@(posedge clk) disable iff (!rstn)
                   $past(rstn) && (!up && !down) |=> count == $past(count));

  // Coverage: wraparound cases
  cover  property (@(posedge clk) disable iff (!rstn)
                   $past(rstn) && $past(up && !down) && ($past(count) == MAX) |=> (count == '0));
  cover  property (@(posedge clk) disable iff (!rstn)
                   $past(rstn) && $past(!up && down) && ($past(count) == '0) |=> (count == MAX));

  // Coverage: reset activity
  cover  property (@(negedge rstn) 1);
  cover  property (@(posedge rstn) 1);
endmodule

bind counter counter_sva #(.WIDTH(WIDTH)) counter_sva_i (.*);