// SVA bind module for sqrt_16bit
// Concise, checks correctness, invariants, and key corner cases.
// Bind this file to the DUT.

module sqrt_16bit_sva (
  input logic [15:0] a,
  input logic        ctrl,
  input logic [15:0] b,
  input logic [15:0] x,
  input logic [3:0]  i,
  input logic [15:0] temp
);

  function automatic int unsigned floor_sqrt16 (input logic [15:0] av);
    int unsigned r = 0;
    for (int k = 7; k >= 0; k--) begin
      int unsigned cand = (r<<1) + (1<<k);
      if (cand*cand <= av) r = cand;
    end
    return r;
  endfunction

  function automatic int unsigned nearest_sqrt16 (input logic [15:0] av);
    int unsigned f  = floor_sqrt16(av);
    int unsigned c  = f + 1;
    int unsigned df = av - f*f;
    int unsigned dc = c*c - av;
    return (dc < df) ? c : f; // ties never occur for integer a
  endfunction

  always @* begin
    // No X/Z on important signals
    assert (!$isunknown({a, ctrl, b, x, i, temp}));

    // Reference model
    int unsigned f = floor_sqrt16(a);
    int unsigned n = nearest_sqrt16(a);

    // Internal invariants (final x is floor(sqrt(a)), 8 iterations done)
    assert (x == f);
    assert (x <= 16'd255);
    assert ((x*x) <= a && ((x+1)*(x+1)) > a);
    assert (i == 4'd8);

    // Output correctness
    assert ((ctrl == 1'b0) -> (b == f));
    assert ((ctrl == 1'b1) -> (b == n));

    // Shape properties by mode
    if (ctrl == 1'b0) begin
      assert ((b*b) <= a && ((b+1)*(b+1)) > a);
    end else begin
      int unsigned df = a - f*f;
      int unsigned dc = (f+1)*(f+1) - a;
      assert (b == f || b == f+1);
      assert (((b==f)   -> (df <= dc)) &&
              ((b==f+1) -> (dc <  df)));
    end

    // Output range
    assert (b <= 16'd256);

    // Functional coverage
    cover (a == 16'd0     && b == 16'd0);
    cover (a == 16'd65025 && ctrl == 1'b0 && b == 16'd255); // 255^2 floor
    cover (a == 16'd65535 && ctrl == 1'b1 && b == 16'd256); // rounds up at max
    cover (ctrl == 1'b1 && b == f);     // rounding down case
    cover (ctrl == 1'b1 && b == f+1);   // rounding up case
    cover (a == 16'd225 && b == 16'd15); // perfect square
  end

endmodule

bind sqrt_16bit sqrt_16bit_sva u_sqrt_16bit_sva (
  .a(a), .ctrl(ctrl), .b(b), .x(x), .i(i), .temp(temp)
);