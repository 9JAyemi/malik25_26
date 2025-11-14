// SVA checker for taxicab_distance
// Bind into the DUT instance: bind taxicab_distance taxicab_distance_sva #(.N(N)) sva();

`ifndef SYNTHESIS
module taxicab_distance_sva #(parameter int N = 32);
  // Visible DUT signals via bind scope
  // x1,y1,x2,y2 : input [N-1:0]
  // dist        : output [N+1:0]
  // dist_x12, dist_x21, dist_xabs, dist_y12, dist_y21, dist_yabs : wire [N:0] signed

  // Expected values (unsigned magnitudes, zero-extended for comparison to signed [N:0])
  logic [N:0] exp_dx, exp_dy;
  logic [N+1:0] exp_dist;

  always_comb begin
    exp_dx   = {1'b0, (x1 >= x2) ? (x1 - x2) : (x2 - x1)};
    exp_dy   = {1'b0, (y1 >= y2) ? (y1 - y2) : (y2 - y1)};
    exp_dist = exp_dx + exp_dy;

    // Core correctness
    assert (dist == exp_dist)
      else $error("taxicab_distance: dist mismatch. exp=%0h got=%0h", exp_dist, dist);

    // Internal muxes implement abs()
    if (x1 >= x2) begin
      assert (dist_xabs == {1'b0,(x1 - x2)})
        else $error("x-abs mux wrong when x1>=x2");
    end else begin
      assert (dist_xabs == {1'b0,(x2 - x1)})
        else $error("x-abs mux wrong when x1<x2");
    end

    if (y1 >= y2) begin
      assert (dist_yabs == {1'b0,(y1 - y2)})
        else $error("y-abs mux wrong when y1>=y2");
    end else begin
      assert (dist_yabs == {1'b0,(y2 - y1)})
        else $error("y-abs mux wrong when y1<y2");
    end

    // Non-negativity of abs terms (signed wires must be positive)
    assert (dist_xabs[N] == 1'b0) else $error("x-abs negative sign bit");
    assert (dist_yabs[N] == 1'b0) else $error("y-abs negative sign bit");

    // No overflow in final sum (N+2 MSB must be 0)
    assert (dist[N+1] == 1'b0) else $error("dist width overflow");

    // Zero-distance iff coordinates equal
    if ((x1 == x2) && (y1 == y2)) begin
      assert (dist == '0) else $error("zero coords but nonzero dist");
      assert (dist_xabs == '0) else $error("x equal but x-abs nonzero");
      assert (dist_yabs == '0) else $error("y equal but y-abs nonzero");
    end
    if (dist == '0) begin
      assert ((x1 == x2) && (y1 == y2)) else $error("zero dist but coords differ");
    end

    // Structural consistency of published equation inside DUT
    assert (dist == dist_xabs + dist_yabs)
      else $error("dist != dist_xabs + dist_yabs");
  end

  // Lightweight functional coverage
  // Compare-path coverage
  always_comb begin
    cover (x1 >  x2);
    cover (x1 <  x2);
    cover (x1 == x2);
    cover (y1 >  y2);
    cover (y1 <  y2);
    cover (y1 == y2);
    // Corner cases
    cover ((x1 == x2) && (y1 == y2)); // zero distance
    cover ((x1 == {N{1'b1}}) && (x2 == '0) && (y1 == '0) && (y2 == {N{1'b1}})); // max distance
    cover ((x1 != x2) && (y1 == y2)); // x-only difference
    cover ((x1 == x2) && (y1 != y2)); // y-only difference
  end
endmodule
`endif