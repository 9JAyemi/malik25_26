// SVA checker for VoltageLevelShifter
// Bind this to the DUT. Provide a simulation clock/reset from TB.
module VoltageLevelShifter_sva #(
  parameter int n = 4,
  parameter int m = 2,
  parameter int R2 = 1000,
  parameter int SHIFT = 10,
  parameter real V1 = 3.3,
  parameter real V2 = 5.0
)(
  input logic clk,
  input logic rst_n,
  input logic [n-1:0] in,
  input logic [m-1:0] out
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Implementation function (matches DUT math)
  function automatic logic [m-1:0] impl_fn(input logic [n-1:0] a);
    logic [n+31:0] prod;
    prod = $unsigned(a) * R2;
    return logic'((prod >> SHIFT)); // truncates to m bits
  endfunction

  // SPEC function: ideal divider ratio equals V1/V2 (since R2/(R1+R2) = V1/V2)
  function automatic logic [m-1:0] spec_fn(input logic [n-1:0] a);
    real r;
    int unsigned q;
    r = $itor($unsigned(a)) * V1 / V2; // ideal continuous
    q = int'($floor(r));               // truncate toward 0 for nonnegative
    return logic'(q[m-1:0]);
  endfunction

  // 1) Check current implementation behavior (golden mirror of DUT)
  assert property (out == impl_fn(in))
    else $error("Impl mismatch: out=%0d exp=%0d in=%0d", $unsigned(out), $unsigned(impl_fn(in)), $unsigned(in));

  // 2) Spec conformance: out should equal floor(in * V1 / V2) (detects wrong scaling)
  assert property (out == spec_fn(in))
    else $error("Spec mismatch (V1/V2): out=%0d exp=%0d in=%0d", $unsigned(out), $unsigned(spec_fn(in)), $unsigned(in));

  // 3) No X/Z on out when in is known
  assert property (!$isunknown(in) |-> !$isunknown(out))
    else $error("X/Z on out with known in: in=%b out=%b", in, out);

  // 4) Monotonicity: nondecreasing mapping (integer truncation allowed)
  assert property (!$isunknown({in,out,$past(in),$past(out)}) && $past(in) <= in |-> out >= $past(out))
    else $error("Non-monotonic: in:%0d->%0d out:%0d->%0d", $unsigned($past(in)), $unsigned(in), $unsigned($past(out)), $unsigned(out));

  // 5) Zero mapping
  assert property (in == '0 |-> out == '0)
    else $error("Zero input did not yield zero output: out=%0d", $unsigned(out));

  // 6) Parameter/width sanity: max expected SPEC value should fit into m bits
  initial begin
    int unsigned exp_max = $unsigned(spec_fn({n{1'b1}}));
    if (exp_max > {m{1'b1}})
      $error("Width m too small: max SPEC value %0d exceeds %0d", exp_max, {m{1'b1}});
  end

  // Coverage
  cover property (in == '0 && out == '0);
  cover property (in == {n{1'b1}} && out == spec_fn({n{1'b1}}));
  // Single-bit input toggle coverage
  cover property (!$isunknown({in,out,$past(in)}) && $changed(in) && $onehot0(in ^ $past(in)));
  // Observe a monotonic increase
  cover property (!$isunknown({in,out,$past(in),$past(out)}) && $past(in) < in && out >= $past(out));

endmodule

// Example bind (provide clk/rst_n from your TB):
// bind VoltageLevelShifter VoltageLevelShifter_sva #(.n(n), .m(m)) u_vls_sva (.* , .clk(tb_clk), .rst_n(tb_rst_n));