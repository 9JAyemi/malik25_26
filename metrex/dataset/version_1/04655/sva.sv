// SVA checker for TrigFunc
// Binds into DUT, uses an event clock on input activity

module TrigFunc_sva #(parameter int n = 10) ();

  // Bind-time visibility of DUT signals (x,y,sum,term,x_pow,fact)
  // Event-driven sampling on input activity
  event ev;
  always @(x) -> ev;

  default clocking cb @ (ev); endclocking

  // Reference model that matches the DUT algorithm bit-for-bit (32-bit modulo arithmetic)
  function automatic logic [31:0] model(input logic [31:0] xi);
    logic [31:0] sum_l, x_pow_l, fact_l, term_l;
    int k;
    sum_l   = 32'd0;
    x_pow_l = xi;
    fact_l  = 32'd1;
    for (k = 0; k < n; k++) begin
      if ((k % 2) == 0) term_l = (x_pow_l / fact_l);
      else              term_l = -(x_pow_l / fact_l);
      sum_l   = sum_l + term_l;
      x_pow_l = x_pow_l * xi * xi;
      fact_l  = fact_l * (2*(k+1)) * (2*(k+1)-1);
    end
    return sum_l;
  endfunction

  // Core functional check: output matches the DUT’s intended algorithm
  assert property (model(x) == y)
    else $error("TrigFunc: y != model(x)");

  // Trivial identity: x==0 => y==0
  assert property ((x == 32'd0) |-> (y == 32'd0))
    else $error("TrigFunc: x==0 but y!=0");

  // No X/Z on output when input is known
  assert property ((!$isunknown(x)) |-> (!$isunknown(y)))
    else $error("TrigFunc: y is X/Z for known x");

  // y mirrors internal sum (combinational assign)
  assert property (y == sum)
    else $error("TrigFunc: y != sum");

  // Last term sign matches loop parity if non-zero
  assert property ((term != 32'd0) |-> (term[31] == ((n % 2) == 0)))
    else $error("TrigFunc: last term sign/parity mismatch");

  // ------------ Coverage ------------
  cover property (x == 32'd0);
  cover property (x == 32'd1);
  cover property (x == 32'hFFFF_FFFF);
  cover property (y == 32'd0 && x != 32'd0);         // cancellation/overflow to zero
  cover property ($isunknown(y));                    // expose divide-by-zero or X-propagation
  cover property (fact == 32'd0);                    // factorial overflow to zero (mod 2^32)
  cover property (x_pow == 32'd0);                   // power overflow/underflow to zero
  cover property (term[31] == 1'b1);                 // negative last term observed

endmodule

// Bind into DUT
bind TrigFunc TrigFunc_sva #(.n(n)) TrigFunc_sva_i;