// SVA for twos_comp: out must be two's complement of in (mod 2^4)
module twos_comp_sva #(parameter int W = 4)
(
  input  logic [W-1:0] in,
  input  logic [W-1:0] out
);

  localparam logic [W-1:0] ONES = {W{1'b1}};
  localparam logic [W-1:0] ONE  = {{(W-1){1'b0}},1'b1};

  // Core functional checks (immediate SVA, combinational)
  always_comb begin
    assert (!$isunknown(in))  else $error("twos_comp: in X/Z");
    assert (!$isunknown(out)) else $error("twos_comp: out X/Z");

    // Definition
    assert (out == ((~in) + ONE)) else
      $error("twos_comp: out != ~in+1: in=%0h out=%0h", in, out);

    // Equivalent invariants
    assert (((in + out) & ONES) == '0) else
      $error("twos_comp: in+out != 0 mod 2^%0d: in=%0h out=%0h sum=%0h", W, in, out, (in+out));
    assert (((~out) + ONE) == in) else
      $error("twos_comp: involution failed: in=%0h out=%0h", in, out);

    // Bit-level sanity (LSB must match)
    assert (out[0] == in[0]) else
      $error("twos_comp: LSB mismatch: in[0]=%0b out[0]=%0b", in[0], out[0]);

    // Key corner cases
    if (in == '0)                     assert (out == '0)      else $error("twos_comp: 0 -> 0 failed");
    if (in == (ONE << (W-1)))         assert (out == (ONE << (W-1))) else $error("twos_comp: MIN_INT -> MIN_INT failed");
    if (in == ONE)                    assert (out == ONES)    else $error("twos_comp: 1 -> all1s failed");
    if (in == ONES)                   assert (out == ONE)     else $error("twos_comp: all1s -> 1 failed");
  end

  // Coverage: see all inputs/outputs and notable mappings
  covergroup cg_in @(in);
    coverpoint in  { bins all[] = {[0:(1<<W)-1]}; }
  endgroup
  covergroup cg_out @(out);
    coverpoint out { bins all[] = {[0:(1<<W)-1]}; }
  endgroup
  cg_in  cin  = new;
  cg_out cout = new;

  always_comb begin
    cover (out == ((~in) + ONE));                 // function evaluated
    cover (in == '0              && out == '0);
    cover (in == (ONE << (W-1))  && out == (ONE << (W-1)));
    cover (in == ONE             && out == ONES);
    cover (in == ONES            && out == ONE);
  end

endmodule

// Bind into the DUT
bind twos_comp twos_comp_sva #(.W(4)) u_twos_comp_sva (.in(in), .out(out));