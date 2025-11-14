// SVA checker for mux4
module mux4_sva (
  input [1:0] sel,
  input [3:0] in0, in1, in2, in3,
  input [3:0] w1, w2, w3, w4,
  input [3:0] out
);

  // X/Z guard
  a_sel_known: assert property (@(*) !$isunknown(sel));

  // Functional correctness per select (and internal masking)
  a_sel00: assert property (@(*) (sel==2'b00) |-> ##0 (out==in0 && w1==in0 && w2==4'b0 && w3==4'b0 && w4==4'b0));
  a_sel01: assert property (@(*) (sel==2'b01) |-> ##0 (out==in1 && w2==in1 && w1==4'b0 && w3==4'b0 && w4==4'b0));
  a_sel10: assert property (@(*) (sel==2'b10) |-> ##0 (out==in2 && w3==in2 && w1==4'b0 && w2==4'b0 && w4==4'b0));
  a_sel11: assert property (@(*) (sel==2'b11) |-> ##0 (out==in3 && w4==in3 && w1==4'b0 && w2==4'b0 && w3==4'b0));

  // Structural OR correctness
  a_out_or: assert property (@(*) ##0 (out == (w1 | w2 | w3 | w4)));

  // No X on out when inputs and sel are known
  a_known_out: assert property (@(*) (!$isunknown(sel) && !$isunknown({in0,in1,in2,in3})) |-> ##0 !$isunknown(out));

  // Minimal functional coverage
  c_sel00: cover property (@(*) (sel==2'b00) && (out==in0));
  c_sel01: cover property (@(*) (sel==2'b01) && (out==in1));
  c_sel10: cover property (@(*) (sel==2'b10) && (out==in2));
  c_sel11: cover property (@(*) (sel==2'b11) && (out==in3));
  c_out_all0: cover property (@(*) out==4'h0);
  c_out_all1: cover property (@(*) out==4'hF);

endmodule

bind mux4 mux4_sva i_mux4_sva (.*);