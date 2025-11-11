// SVA for priority_encoder (concise, quality-focused)
// Bind this to the DUT to check correctness and collect coverage.

module priority_encoder_sva #(parameter int n = 8)
(
  input logic [n-1:0] in,
  input logic [($clog2(n)-1):0] out
);

  typedef logic [($clog2(n)-1):0] out_t;

  // The DUT implementation is hardcoded for n==8 (case items and 3-bit literals)
  initial assert (n == 8)
    else $error("priority_encoder: implementation is hardcoded for n==8, got n=%0d", n);

  // Compute expected priority-encoded output:
  // - Highest set bit has highest priority (MSB wins)
  // - out = (n-1 - msb_index); for in==0 -> 0
  function automatic int msb_index(input logic [n-1:0] v);
    int i;
    for (i = n-1; i >= 0; i--) if (v[i] === 1'b1) return i;
    return -1; // none set
  endfunction

  function automatic out_t expected_out(input logic [n-1:0] v);
    int idx = msb_index(v);
    if (idx < 0) return '0;
    else return out_t'((n-1) - idx);
  endfunction

  // Core combinational correctness check (skip X/Z on inputs)
  always_comb begin
    if (!$isunknown(in)) begin
      assert (out == expected_out(in))
        else $error("priority_encoder mismatch: in=%0b out=%0h exp=%0h", in, out, expected_out(in));
      assert (!$isunknown(out))
        else $error("priority_encoder produced X/Z on known input: in=%0b out=%0h", in, out);
    end
  end

  // Functional coverage
  // - default case
  always_comb cover (!$isunknown(in) && in == '0 && out == '0);

  // - each one-hot input bit maps correctly
  genvar k;
  generate
    for (k = 0; k < n; k++) begin : cov_onehot
      localparam logic [n-1:0] OH = logic'(1) << k;
      always_comb cover (!$isunknown(in) && in == OH && out == expected_out(in));
    end
  endgenerate

  // - at least one multi-bit case is prioritized correctly
  always_comb cover (!$isunknown(in) && $countones(in) >= 2 && out == expected_out(in));

endmodule

bind priority_encoder priority_encoder_sva #(.n(n)) pe_sva_b (.in(in), .out(out));