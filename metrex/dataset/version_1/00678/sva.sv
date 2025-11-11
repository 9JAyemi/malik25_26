// SVA checker for ch_eq — concise, focuses on key correctness, hazards, and basic coverage
module ch_eq_sva #(parameter int n=4, m=2)
(
  input  logic [n-1:0] in,
  input  logic [m-1:0] chan,
  input  logic [n-1:0] out
);

  // Recompute DUT expression exactly (including truncation)
  logic [n-1:0] inv_calc;
  logic [2*n-1:0] prod_full;
  logic [n-1:0] exp_out;

  always_comb begin
    // Sanity: no X/Z on inputs
    assert (!$isunknown({in,chan})) else $error("ch_eq: X/Z on in/chan");

    // Environment constraint: avoid divide-by-zero (DUT would produce X)
    assume (chan != '0);

    // Expected computation (mirror DUT semantics)
    inv_calc  = ({n{1'b0}} / chan);
    prod_full = in * inv_calc;
    exp_out   = prod_full[n-1:0];

    // Functional equivalence (bit-accurate, including truncation)
    assert (out === exp_out) else
      $error("ch_eq: out != truncated(in * inv_freq_resp(chan))");

    // Zero-input property
    if (in == '0) assert (out == '0) else
      $error("ch_eq: in==0 but out!=0");

    // Output should be known when inputs are known
    assert (!$isunknown(out)) else
      $error("ch_eq: X/Z on out with known inputs");

    // If the inverse equals unity, output must equal input
    if (inv_calc == {{(n-1){1'b0}},1'b1}) assert (out == in) else
      if (inv_calc == {{(n-1){1'b0}},1'b1}) $error("ch_eq: inv==1 but out!=in");

    // Lightweight coverage (combinational sampling)
    cover (!($isunknown({in,chan,out})));
    cover (in == '0);
    cover (chan == '0);      // should be unreachable under assume; flags stimulus hitting the hazard
    cover (out == '0);
    cover (inv_calc == {{(n-1){1'b0}},1'b1});  // unity inverse case
  end

endmodule

// Bind checker to DUT
bind ch_eq ch_eq_sva #(.n(n), .m(m)) u_ch_eq_sva (.*);