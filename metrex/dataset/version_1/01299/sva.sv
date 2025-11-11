// SVA for addfxp: end-to-end correctness, pipeline integrity, and key coverage
module addfxp_sva #(parameter int width=16, cycles=1)
(
  input  logic                         clk,
  input  logic signed [width-1:0]      a,
  input  logic signed [width-1:0]      b,
  input  logic signed [width-1:0]      q,
  input  logic signed [width-1:0]      res [cycles-1:0]
);

  default clocking @(posedge clk); endclocking

  // Basic interface sanity
  a_no_x:    assert property (!$isunknown(a));
  b_no_x:    assert property (!$isunknown(b));

  // Combinational tie-off
  q_tie:     assert property (q == res[cycles-1]);

  // res[0] captures a+b on the previous cycle (NBA semantics)
  cap_add:   assert property ($past(1'b1,1,1'b0) |-> res[0] == $past(a,1) + $past(b,1));

  // Pipeline shift correctness
  genvar i;
  generate
    for (i=1; i<cycles; i++) begin : g_shift
      shift_ok: assert property ($past(1'b1,1,1'b0) |-> res[i] == $past(res[i-1],1));
    end
  endgenerate

  // End-to-end latency: q equals a+b delayed by cycles
  lat_ok:    assert property ($past(1'b1,cycles,1'b0) |-> q == $past(a,cycles) + $past(b,cycles));

  // Coverage: nontrivial add observed
  cov_add:   cover property ($past(1'b1,1,1'b0) && ( $past(a,1)!=0 || $past(b,1)!=0 ) && res[0]!=0);

  // Coverage: signed overflow at res[0]
  cov_ovf:   cover property ($past(1'b1,1,1'b0) &&
                             ($past(a[width-1],1) == $past(b[width-1],1)) &&
                             (res[0][width-1] != $past(a[width-1],1)));

  // Coverage: pipeline propagation (only meaningful if cycles>1)
  generate if (cycles>1) begin
    cov_pipe: cover property ($changed(res[0]) ##1 $changed(res[1]));
  end endgenerate

endmodule

// Bind into the DUT
bind addfxp addfxp_sva #(.width(width), .cycles(cycles))
  (.clk(clk), .a(a), .b(b), .q(q), .res(res));