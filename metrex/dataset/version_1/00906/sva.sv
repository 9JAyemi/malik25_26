// SVA for the given design. Bind these to the DUT; no DUT changes needed.

// odd_parity_generator
module odd_parity_generator_sva (input [7:0] in, input [8:0] out);
  always_comb begin
    assert (out[7:0] == in) else $error("odd_parity_generator: out[7:0] != in");
    assert (out[8]   == ^in) else $error("odd_parity_generator: out[8] != ^in");
    assert ((^out)   == 1'b0) else $error("odd_parity_generator: total parity not even");
  end
endmodule
bind odd_parity_generator odd_parity_generator_sva (.in(in), .out(out));

// bcd_counter
module bcd_counter_sva (input clk, input reset, input [2:0] ena, input [3:0] q);
  // async reset to 0
  assert property (@(posedge reset) q == 4'd0);
  // hold at 0 while reset asserted
  assert property (@(posedge clk) reset |-> q == 4'd0);

  // ena[2] branch: BCD 0..9 with wrap
  assert property (@(posedge clk) disable iff (reset)
                   ena[2] |=> q == (($past(q) == 4'd9) ? 4'd0 : $past(q) + 4'd1));

  // ena[1] branch: custom sequence
  assert property (@(posedge clk) disable iff (reset)
                   !ena[2] && ena[1] |=> q ==
                     ( ($past(q[3]) && ($past(q[2:0]) == 3'b011)) ? 4'd0 :
                       ($past(q[2:0]) == 3'b100)                  ? 4'd8 :
                                                                    $past(q) + 4'd1 ));

  // ena[0] branch: saturate at 8
  assert property (@(posedge clk) disable iff (reset)
                   !ena[2] && !ena[1] && ena[0] |=> q ==
                     ( ($past(q[3:1]) == 3'b100) ? 4'd8 : $past(q) + 4'd1 ));

  // no enable: hold
  assert property (@(posedge clk) disable iff (reset)
                   !ena[2] && !ena[1] && !ena[0] |=> q == $past(q));

  // coverage
  cover property (@(posedge clk) disable iff (reset) (ena[2] && $past(q) == 4'd9) |=> q == 4'd0);
  cover property (@(posedge clk) disable iff (reset) (ena[2] && $past(q) != 4'd9) |=> q == $past(q) + 4'd1);
  cover property (@(posedge clk) disable iff (reset) (!ena[2] && ena[1] && $past(q) == 4'd4)  |=> q == 4'd8);
  cover property (@(posedge clk) disable iff (reset) (!ena[2] && ena[1] && $past(q) == 4'd11) |=> q == 4'd0);
  cover property (@(posedge clk) disable iff (reset)
                  (!ena[2] && ena[1] &&
                   !($past(q[3]) && $past(q[2:0]) == 3'b011) &&
                   !($past(q[2:0]) == 3'b100)) |=> q == $past(q) + 4'd1);
  cover property (@(posedge clk) disable iff (reset) (!ena[2] && !ena[1] && ena[0] && $past(q) == 4'd7) |=> q == 4'd8);
  cover property (@(posedge clk) disable iff (reset) (!ena[2] && !ena[1] && ena[0] && $past(q) == 4'd8) |=> q == 4'd8);
endmodule
bind bcd_counter bcd_counter_sva (.clk(clk), .reset(reset), .ena(ena), .q(q));

// adder
module adder_sva (input [8:0] a, input [3:0] b, input [7:0] out);
  always_comb begin
    assert (out == a[7:0] + b) else $error("adder: out != a[7:0] + b");
  end
endmodule
bind adder adder_sva (.a(a), .b(b), .out(out));

// top_module
module top_module_sva (input clk, input reset,
                       input [7:0] in,
                       input [8:0] parity_out,
                       input [2:0] ena,
                       input [15:0] q,
                       input [7:0] add_out);
  // wiring/tie-offs
  assert property (@(posedge clk) parity_out[7:0] == in);
  assert property (@(posedge clk) parity_out[8]   == ^in);
  assert property (@(posedge clk) (^parity_out)   == 1'b0);
  assert property (@(posedge clk) q[15:4] == 12'h000);
  assert property (@(posedge clk) ena == 3'b000);
  assert property (@(posedge clk) add_out == (in + q[3:0]));

  // with ena tied low, low nibble holds (after reset)
  assert property (@(posedge clk) disable iff (reset)
                   (ena == 3'b000) |=> q[3:0] == $past(q[3:0]));

  // async reset drives low nibble to 0 via counter
  assert property (@(posedge reset) q[3:0] == 4'd0);

  // coverage: both parity cases; adder overflow wrap
  cover property (@(posedge clk) (^in) == 1'b0);
  cover property (@(posedge clk) (^in) == 1'b1);
  cover property (@(posedge clk) add_out < in);
endmodule
bind top_module top_module_sva (.clk(clk), .reset(reset), .in(in),
                                .parity_out(parity_out), .ena(ena), .q(q), .add_out(add_out));