// SVA for rotator/top_module
// Focused, concise checks + essential coverage

module rotator_sva(
  input logic         clk,
  input logic         load,
  input logic [1:0]   ena,
  input logic [99:0]  data,
  input logic [99:0]  q
);
  default clocking cb @(posedge clk); endclocking

  // Load has priority
  assert property ($past(load) |-> (q == $past(data)));

  // Rotate-left by 1 when ena==2'b00 and not loading
  assert property ($past(!load && (ena==2'b00))
                   |-> (q == {$past(q)[98:0], $past(q)[99]}));

  // Hold otherwise (ena != 2'b00), including ena==2'b01 and default
  assert property ($past(!load && (ena!=2'b00)) |-> (q == $past(q)));

  // 100 consecutive left-rotates return to original value
  sequence rot_left_cyc; !load && (ena==2'b00); endsequence
  assert property (rot_left_cyc[*100] |=> (q == $past(q,100)));

  // Known propagation after a known load
  assert property ($past(load) && !$isunknown($past(data)) |-> !$isunknown(q));

  // Coverage
  cover property ($past(load) && (q == $past(data)));                         // load
  cover property ($past(!load && ena==2'b00) &&                               // rotate-left
                  (q == {$past(q)[98:0], $past(q)[99]}));
  cover property ($past(!load && ena==2'b01) && (q == $past(q)));             // hold on 01
  cover property ($past(!load && (ena inside {2'b10,2'b11})) && (q==$past(q)));// hold default
  // Wrap-around example: 1 at MSB moves to LSB on left-rotate
  cover property ($past(!load && ena==2'b00) &&
                  ($past(q) == (100'b1 << 99)) && (q == 100'b1));
endmodule

// Bind into DUT (choose one)
bind top_module  rotator_sva rotator_sva_i (.clk(clk), .load(load), .ena(ena), .data(data), .q(q));
// Alternatively:
// bind rotator     rotator_sva rotator_sva_i (.clk(clk), .load(load), .ena(ena), .data(data), .q(q));