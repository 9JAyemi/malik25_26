// SVA checker for DEMUX. Bind this to the DUT.
// This will flag the bug where out[0] always follows in regardless of sel.

module demux_sva #(parameter int n = 4)
(
  input  logic                       in,
  input  logic [clogb2(n)-1:0]       sel,
  input  logic [n-1:0]               out
);

  // match DUT's width computation
  function automatic int clogb2(input int number);
    clogb2 = 0;
    while (number > 0) begin
      number = number >> 1;
      clogb2 = clogb2 + 1;
    end
  endfunction

  function automatic logic [n-1:0] onehot_from_sel(input logic [clogb2(n)-1:0] s);
    logic [n-1:0] v;
    v = '0;
    if (s < n) v[s] = 1'b1;
    return v;
  endfunction

  // Inputs must be known for functional checks
  a_no_x_inputs:  assert property (@*) !$isunknown({in, sel});

  // Legal select range (tighten or convert to assume if needed)
  a_sel_in_range: assert property (@*) sel < n;

  // Zero input drives all zeros
  a_zero_input_clears: assert property (@*) (!in) |-> (out == '0);

  // Demux functional equivalence (strongest check)
  a_demux_functional: assert property (@*)
                      (in && (sel < n)) |-> (out == onehot_from_sel(sel));

  // Onehot-0 shape at all times; with in==1 this enforces at most one bit set
  a_onehot0_shape:    assert property (@*) $onehot0(out);

  // No X/Z propagation when inputs are known
  a_no_x_propagation: assert property (@*) (!$isunknown({in, sel})) |-> !$isunknown(out);

  // Per-bit checks
  genvar i;
  generate
    for (i = 0; i < n; i++) begin : bit_checks
      a_bit_follows_sel: assert property (@*) (sel == i) |-> (out[i] == in);
      a_other_bits_zero: assert property (@*) (in && (sel != i) && (sel < n)) |-> (out[i] == 1'b0);
      c_hit_each_sel:    cover  property (@*) (in && (sel == i));
    end
  endgenerate

  // Basic input coverage
  c_in0: cover property (@*) !in;
  c_in1: cover property (@*)  in;

endmodule

// Bind into the DUT
bind DEMUX demux_sva #(.n(n)) demux_sva_i (.in(in), .sel(sel), .out(out));