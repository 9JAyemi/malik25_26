// SVA for ClockGenerator
module ClockGenerator_sva #(parameter int COUNT_50MHZ = 100,
                            parameter int COUNT_100MHZ = 50)
(
  input  logic        clk_in,
  input  logic        clk_out,
  input  logic [7:0]  counter,
  input  logic [31:0] count,
  input  logic [31:0] expected_count,
  input  logic        locked
);

  localparam int HALF_DIV = COUNT_100MHZ + 1;

  // Start flags to make $past safe
  logic started_in, started_out;
  initial begin started_in = 0; started_out = 0; end
  always @(posedge clk_in)  started_in  <= 1'b1;
  always @(posedge clk_out) started_out <= 1'b1;

  // ---------------- clk_in domain (clock generation) ----------------
  // counter next-state and clk_out behavior
  assert property (@(posedge clk_in) disable iff (!started_in)
                   (counter != COUNT_100MHZ) |=> (counter == $past(counter)+1 && clk_out == $past(clk_out)));

  assert property (@(posedge clk_in) disable iff (!started_in)
                   (counter == COUNT_100MHZ) |=> (counter == 0 && clk_out != $past(clk_out)));

  // counter stays in range 0..COUNT_100MHZ
  assert property (@(posedge clk_in) disable iff (!started_in)
                   counter <= COUNT_100MHZ);

  // Exact spacing of toggle events (half-period = COUNT_100MHZ+1 clk_in cycles)
  assert property (@(posedge clk_in) disable iff (!started_in)
                   (counter == COUNT_100MHZ) |-> (counter != COUNT_100MHZ)[*COUNT_100MHZ] ##1 (counter == COUNT_100MHZ));

  // clk_out changes only coincident with clk_in posedge (no glitches)
  assert property (@(posedge clk_out) disable iff (!started_out) $rose(clk_in));
  assert property (@(negedge clk_out) disable iff (!started_out) $rose(clk_in));

  // ---------------- clk_out domain (frequency checker block) ----------------
  // count next-state and range
  assert property (@(posedge clk_out) disable iff (!started_out)
                   (count != COUNT_50MHZ) |=> count == $past(count)+1);
  assert property (@(posedge clk_out) disable iff (!started_out)
                   (count == COUNT_50MHZ) |=> count == 0);
  assert property (@(posedge clk_out) disable iff (!started_out)
                   count <= COUNT_50MHZ);

  // count boundary spacing (COUNT_50MHZ+1 clk_out cycles)
  assert property (@(posedge clk_out) disable iff (!started_out)
                   (count == COUNT_50MHZ) |-> (count != COUNT_50MHZ)[*COUNT_50MHZ] ##1 (count == COUNT_50MHZ));

  // expected_count update protocol
  assert property (@(posedge clk_out) disable iff (!started_out)
                   (count != COUNT_50MHZ) |=> expected_count == $past(expected_count));

  assert property (@(posedge clk_out) disable iff (!started_out)
                   (count == COUNT_50MHZ && expected_count == 0) |=> expected_count == COUNT_50MHZ);

  assert property (@(posedge clk_out) disable iff (!started_out)
                   (count == COUNT_50MHZ && expected_count == COUNT_50MHZ) |=> expected_count == COUNT_100MHZ);

  assert property (@(posedge clk_out) disable iff (!started_out)
                   (count == COUNT_50MHZ && expected_count == COUNT_100MHZ) |=> expected_count == COUNT_50MHZ);

  // locked update only at boundary and matches compare result
  assert property (@(posedge clk_out) disable iff (!started_out)
                   (count != COUNT_50MHZ) |=> locked == $past(locked));

  assert property (@(posedge clk_out) disable iff (!started_out)
                   (count == COUNT_50MHZ) |=> locked == (expected_count == COUNT_50MHZ));

  // ---------------- Coverage ----------------
  // See at least two clk_out toggles spaced correctly
  cover property (@(posedge clk_in) disable iff (!started_in)
                  (counter == COUNT_100MHZ) ##1 (counter == 0) ##(COUNT_100MHZ) (counter == COUNT_100MHZ));

  // See expected_count sequence 0 -> 100 -> 50 and locked asserted
  cover property (@(posedge clk_out) disable iff (!started_out)
                  (count == COUNT_50MHZ && expected_count == 0)
                  ##1 (expected_count == COUNT_50MHZ)
                  ##[1:$] (count == COUNT_50MHZ && expected_count == COUNT_50MHZ)
                  ##1 (expected_count == COUNT_100MHZ)
                  ##[1:$] (count == COUNT_50MHZ && expected_count == COUNT_100MHZ)
                  ##1 (expected_count == COUNT_50MHZ) ##0 locked);

endmodule

// Bind into DUT (uses DUT's localparams by name)
bind ClockGenerator ClockGenerator_sva #(.COUNT_50MHZ(COUNT_50MHZ),
                                         .COUNT_100MHZ(COUNT_100MHZ))
  u_clockgen_sva(.clk_in(clk_in),
                 .clk_out(clk_out),
                 .counter(counter),
                 .count(count),
                 .expected_count(expected_count),
                 .locked(locked));