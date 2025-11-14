// SVA checker for CRC. Bind this to the DUT.
module crc_sva #(parameter int n=8, m=16, k=16)
(
  input logic                   clk,
  input logic [n-1:0]           in,
  input logic [m-1:0]           out,
  input logic [k-1:0]           gen_poly,
  input logic [k-1:0]           crc_reg
);

  // Parameter sanity at elaboration
  initial begin
    assert (k >= n) else $fatal(1, "CRC: k (%0d) must be >= n (%0d)", k, n);
    assert (m == 2*n) else $fatal(1, "CRC: m (%0d) must equal 2*n (%0d)", m, 2*n);
  end

  // Golden next-state function (matches DUT algorithm)
  function automatic [k-1:0] crc_step(input [k-1:0] s, input [n-1:0] d, input [k-1:0] p);
    automatic [k-1:0] t;
    int i;
    begin
      t = {d, s[k-1:n]};
      for (i = 0; i < n; i++) begin
        if (t[k-1]) t ^= p;
        t = t << 1;
      end
      return t;
    end
  endfunction

  default clocking cb @(posedge clk); endclocking

  // Basic X/const checks
  assert property (!$isunknown(in));
  assert property (!$isunknown(gen_poly));
  assert property ($stable(gen_poly));           // poly should be constant
  assert property (gen_poly[k-1] && gen_poly[0]); // polynomial ends must be 1

  // Out upper n bits must mirror input of same cycle (visible as $past at assertion time)
  assert property (out[m-1 -: n] == $past(in));

  // Full out correctness vs golden model (guard unknown history)
  assert property (
    !$isunknown($past(in)) && !$isunknown($past(crc_reg)) && !$isunknown($past(gen_poly))
    |->
    out == { $past(in), crc_step($past(crc_reg), $past(in), $past(gen_poly))[n-1:0] }
  );

  // Internal state progression matches golden model across cycles
  assert property (
    !$isunknown($past(crc_reg,2)) && !$isunknown($past(in)) && !$isunknown($past(gen_poly))
    |->
    $past(crc_reg) == crc_step($past(crc_reg,2), $past(in), $past(gen_poly))
  );

  // No X on output once driving inputs/poly have been known for one cycle
  assert property (
    !$isunknown($past(in)) && !$isunknown($past(gen_poly)) && !$isunknown($past(crc_reg))
    |->
    !$isunknown(out)
  );

  // Functional coverage
  cover property (in == '0);
  cover property (in == {n{1'b1}});
  cover property (in[n-1] == 1'b1);     // exercises XOR path in first loop iteration
  cover property (in[n-1] == 1'b0);     // exercises no-XOR path
  cover property (out != $past(out));   // output activity

endmodule

// Bind to the DUT (assumes signal names match)
bind CRC crc_sva #(.n(n), .m(m), .k(k)) u_crc_sva (.*);