// SVA for module bullet
// Bind this module to bullet: bind bullet bullet_sva #(w,s) i_bullet_sva(.*);

module bullet_sva #(parameter w=4, s=4) (
  input clk, rst,
  input [10:0] x, y, poX, poY,
  input trigger, timer, d,
  input bullet,
  input [10:0] nowX, nowY,
  input start, over
);

default clocking cb @(posedge clk); endclocking

// Asynchronous reset holds all cleared while asserted
assert property (@(posedge clk) rst |-> (start==0 && over==0 && nowX==0 && nowY==0 && bullet==0));

// Start behavior
assert property (@(posedge clk) disable iff (rst) trigger |=> start);
assert property (@(posedge clk) disable iff (rst) start |=> start); // sticky until rst

// nowX updates
assert property (@(posedge clk) disable iff (rst) trigger |=> nowX == $past(poX));
assert property (@(posedge clk) disable iff (rst)
                 (timer && start && !trigger) |=> nowX == ($past(nowX) + ($past(d) ? w : -w)));
assert property (@(posedge clk) disable iff (rst)
                 (!trigger && (!timer || !start)) |=> nowX == $past(nowX));

// nowY updates
assert property (@(posedge clk) disable iff (rst) trigger |=> nowY == $past(poY));
assert property (@(posedge clk) disable iff (rst) !trigger |=> nowY == $past(nowY));

// over behavior: set conditions, monotonicity, and no spurious rise
assert property (@(posedge clk) disable iff (rst)
                 ($rose(over)) |-> $past( (d && start && (nowX > 11'd904)) ||
                                           (!d && start && (nowX < 11'd104) && (nowX > 11'd0)) ));
assert property (@(posedge clk) disable iff (rst)
                 (d && start && (nowX > 11'd904)) |=> over);
assert property (@(posedge clk) disable iff (rst)
                 (!d && start && (nowX < 11'd104) && (nowX > 11'd0)) |=> over);
assert property (@(posedge clk) disable iff (rst) over |=> over); // once 1, stays 1 until rst

// Bullet combinational intent (registered): next bullet equals predicate of current cycle
wire hit_r = d && start &&
             (x < (nowX + w + 11'd36)) && (x > (nowX + 11'd36)) &&
             (y < (nowY + w + 11'd20)) && (y > (nowY + 11'd20));
wire hit_l = !d && start &&
             (x < (nowX + w)) && (x > nowX) &&
             (y < (nowY + w + 11'd20)) && (y > (nowY + 11'd20));

assert property (@(posedge clk) disable iff (rst)
                 bullet == $past((!over) && (hit_r || hit_l)));

// Coverage
cover property (@(posedge clk) disable iff (rst) trigger ##1 start);
cover property (@(posedge clk) disable iff (rst) (timer && start && d && !trigger) ##1 (nowX == $past(nowX) + w));
cover property (@(posedge clk) disable iff (rst) (timer && start && !d && !trigger) ##1 (nowX == $past(nowX) - w));
cover property (@(posedge clk) disable iff (rst) (start && d && (nowX > 11'd904)) ##1 over);
cover property (@(posedge clk) disable iff (rst) (start && !d && (nowX < 11'd104) && (nowX > 11'd0)) ##1 over);
cover property (@(posedge clk) disable iff (rst) ((!over) && hit_r) ##1 bullet);
cover property (@(posedge clk) disable iff (rst) ((!over) && hit_l) ##1 bullet);

endmodule

// Bind example (place in a scope that sees both modules):
// bind bullet bullet_sva #(w,s) i_bullet_sva(.*);