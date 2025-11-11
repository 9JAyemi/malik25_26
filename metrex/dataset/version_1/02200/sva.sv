// SVA for INV4BITS — concise, high-quality checks and coverage

checker INV4BITS_sva (input logic [3:0] in, input logic [3:0] out);

  // Functional equivalence (4-state) and X-prop sanity
  always_comb begin
    assert (#0) (out === ~in)
      else $error("INV4BITS: out != ~in (out=%b in=%b)", out, in);
    if (!$isunknown(in)) assert (!$isunknown(out))
      else $error("INV4BITS: out has X/Z while in is known (out=%b in=%b)", out, in);
  end

  // Bit-level instantaneous edge correlation (no glitches, correct polarity)
  genvar i;
  for (i=0; i<4; i++) begin : g
    ap_in_r: assert property (disable iff ($isunknown(in[i]) || $isunknown(out[i]))
                              @(posedge in[i]) (out[i] === ~in[i]) and $fell(out[i]))
      else $error("INV4BITS bit%0d: posedge in not mirrored as negedge out", i);

    ap_in_f: assert property (disable iff ($isunknown(in[i]) || $isunknown(out[i]))
                              @(negedge in[i]) (out[i] === ~in[i]) and $rose(out[i]))
      else $error("INV4BITS bit%0d: negedge in not mirrored as posedge out", i);

    ap_out_r_src: assert property (disable iff ($isunknown(in[i]) || $isunknown(out[i]))
                                   @(posedge out[i]) (in[i] === ~out[i]) and $fell(in[i]))
      else $error("INV4BITS bit%0d: posedge out without negedge in", i);

    ap_out_f_src: assert property (disable iff ($isunknown(in[i]) || $isunknown(out[i]))
                                   @(negedge out[i]) (in[i] === ~out[i]) and $rose(in[i]))
      else $error("INV4BITS bit%0d: negedge out without posedge in", i);
  end

  // Functional coverage: all input values and per-bit toggles
  covergroup cg_in @(in);
    coverpoint in { bins all_vals[] = {[0:15]}; }
  endgroup
  cg_in cg = new();

  for (genvar j=0; j<4; j++) begin : c
    cover property (@(posedge in[j]) 1);
    cover property (@(negedge in[j]) 1);
  end
endchecker

bind INV4BITS INV4BITS_sva sva_i (.in(in), .out(out));