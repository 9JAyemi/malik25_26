`timescale 1ns/1ps

module edge_detector_sva();

  logic clk;
  logic [7:0] in;
  logic [7:0] out;

  edge_detector dut (
    .clk(clk),
    .in(in),
    .out(out)
  );

  // clock
  initial clk = 0;
  always #5 clk = ~clk;

  // When input changes (curr_in != prev_in), FSM should transition to state 3'b001
  always @(posedge clk) begin
    if (dut.curr_in != dut.prev_in)
      assert (dut.state == 3'b001) else $error("Change not detected: prev=%b curr=%b state=%b", dut.prev_in, dut.curr_in, dut.state);
  end

  // Check FSM progression
  always @(posedge clk) begin
    if (dut.state == 3'b001)
      assert ($past(dut.state) != 3'b001 || dut.state == 3'b010) else $error("State did not progress 001->010");
    if (dut.state == 3'b010)
      assert ($past(dut.state) != 3'b010 || dut.state == 3'b011) else $error("State did not progress 010->011");
    if (dut.state == 3'b011)
      assert (out == dut.next_in) else $error("out != next_in when in state 011: out=%b next_in=%b", out, dut.next_in);
  end

  // Shift-register behavior across posedges
  always @(posedge clk) begin
    assert (dut.prev_in == $past(dut.curr_in)) else $error("prev_in didn't capture curr_in");
    assert (dut.curr_in == $past(dut.next_in)) else $error("curr_in didn't capture next_in");
    assert (dut.next_in == $past(in)) else $error("next_in didn't capture in");
  end

  // small stimulus for simulation
  initial begin
    in = 8'h00; #20;
    in = 8'hFF; #100;
    in = 8'h0F; #100;
    $finish;
  end

endmodule
