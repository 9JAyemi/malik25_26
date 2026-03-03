// SVA for twos_complement
module twos_complement_sva(input [3:0] in, input [3:0] out);

  // Functional correctness (allow 0-delay settle)
  a_func: assert property (@(in) ##0 (out == ((~in) + 4'd1)))
    else $error("twos_complement func mismatch: in=%0h out=%0h exp=%0h", in, out, ((~in)+4'd1));

  // Sum-zero invariant (mod-16)
  a_sum_zero: assert property (@(in or out) ##0 (!$isunknown({in,out}) |-> ((in + out) == 4'd0)))
    else $error("in+out != 0 (mod 16): in=%0h out=%0h sum=%0h", in, out, (in+out));

  // No X/Z on out when in is known
  a_no_x: assert property (@(in or out) ##0 (!$isunknown(in) |-> !$isunknown(out)))
    else $error("out has X/Z while in is known: in=%0h out=%0h", in, out);

  // Full input value coverage
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : C_IN_ALL
      c_in_val: cover property (@(in) (!$isunknown(in) && (in == i[3:0])));
    end
  endgenerate

  // Special-case coverage: 0 -> 0, 8 -> 8
  c_zero: cover property (@(in or out) ##0 (!$isunknown({in,out}) && in==4'h0 && out==4'h0));
  c_min:  cover property (@(in or out) ##0 (!$isunknown({in,out}) && in==4'h8 && out==4'h8));

endmodule

// Bind into DUT
bind twos_complement twos_complement_sva sva_inst (.in(in), .out(out));