// SVA for counter
module counter_sva #(parameter WIDTH=4)
(
  input  logic                clk,
  input  logic                rst,
  input  logic                en,
  input  logic                up,
  input  logic [WIDTH-1:0]    count
);

  default clocking cb @(posedge clk); endclocking

  // Asynchronous reset behavior
  assert property (@(posedge rst) count == '0);
  assert property (rst |-> count == '0);

  // Sanity: no X on controls/data after reset
  assert property (disable iff (rst) !$isunknown(en) && !$isunknown(up));
  assert property (disable iff (rst) !$isunknown(count));

  // Hold when disabled
  assert property (disable iff (rst) !en |-> $stable(count));

  // Count updates when enabled
  assert property (disable iff (rst) en && up  |-> count == $past(count) + 1'b1);
  assert property (disable iff (rst) en && !up |-> count == $past(count) - 1'b1);

  // Change only when enabled (excluding reset)
  assert property (disable iff (rst) $changed(count) |-> en);

  // Coverage
  cover property (@(posedge rst) count == '0);                                   // async reset seen
  cover property (disable iff (rst) en && up);                                   // increment enabled
  cover property (disable iff (rst) en && !up);                                  // decrement enabled
  cover property (disable iff (rst) !en ##1 $stable(count));                     // hold
  cover property (disable iff (rst) $past(count)=={WIDTH{1'b1}} && en && up
                                  ##1 count=='0);                                // wrap up
  cover property (disable iff (rst) $past(count)=='0 && en && !up
                                  ##1 count=={WIDTH{1'b1}});                     // wrap down
  cover property (disable iff (rst) en && up ##1 en && !up);                     // dir flip up->down
  cover property (disable iff (rst) en && !up ##1 en && up);                     // dir flip down->up
endmodule

// Bind into DUT
bind counter counter_sva #(.WIDTH(4)) u_counter_sva (
  .clk  (clk),
  .rst  (rst),
  .en   (en),
  .up   (up),
  .count(count)
);