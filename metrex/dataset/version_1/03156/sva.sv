// SVA checker for bcd_to_7segment_decoder
module bcd_to_7segment_decoder_sva #(parameter bit ENABLE_COV=1)
(
  input logic [3:0] x,
  input logic [3:0] an,
  input logic [6:0] seg
);

  // Golden reference (from DUT equations)
  function automatic logic [6:0] seg_ref(input logic [3:0] x);
    logic [6:0] r;
    r[0] = (~x[0] & ~x[1] & x[2]) | (x[0] & ~x[1] & ~x[2] & ~x[3]);
    r[1] = (x[0] ^ x[1]) & x[2];
    r[2] = ~x[0] & x[1] & ~x[2];
    r[3] = (~x[0] & ~x[1] & x[2]) | (x[0] & ~x[1] & ~x[2] & ~x[3]) | (x[0] & x[1] & x[2]);
    r[4] = (x[0]) | (~x[0] & ~x[1] & x[2]);
    r[5] = (x[0] & x[1]) | (x[1] & ~x[2]) | (x[0] & ~x[2] & ~x[3]);
    r[6] = (x[0] & x[1] & x[2]) | (~x[1] & ~x[2] & ~x[3]);
    return r;
  endfunction

  // Combinational equivalence checks (delta-cycle settled)
  always_comb begin
    assert (#0 an == 4'b0001)
      else $error("bcd7seg an mismatch: an=%b", an);
    assert (#0 seg == seg_ref(x))
      else $error("bcd7seg seg mismatch: x=%h seg=%b exp=%b", x, seg, seg_ref(x));
  end

  // Event to sample assertions/coverage when inputs change
  event ev_x; always @(x) -> ev_x;
  default clocking cb @(ev_x); endclocking

  // No X/Z on outputs when inputs are known
  assert property (cb !$isunknown(x) |-> (!$isunknown(seg) && !$isunknown(an)))
    else $error("bcd7seg X/Z on outputs for known x: x=%h seg=%b an=%b", x, seg, an);

  // Coverage: all input combinations; each seg bit can be 0/1; an constant seen
  generate if (ENABLE_COV) begin : COV
    genvar i,b;
    for (i=0; i<16; i++) begin : C_X
      cover property (cb x == i[3:0]);
    end
    for (b=0; b<7; b++) begin : C_SEG
      cover property (cb seg[b] == 1'b0);
      cover property (cb seg[b] == 1'b1);
    end
    cover property (cb an == 4'b0001);
  end endgenerate

endmodule

// Bind into DUT
bind bcd_to_7segment_decoder bcd_to_7segment_decoder_sva sva_bcd7seg (.x(x), .an(an), .seg(seg));