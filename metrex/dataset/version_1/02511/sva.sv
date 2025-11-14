// SVA checker for decoder_3to8
module decoder_3to8_sva (
  input A,
  input B,
  input C,
  input [7:0] Y
);

  // Evaluate on any input change; use ##0 to avoid delta races w/ continuous assigns
  // Functional correctness and no-X on outputs when inputs are known
  a_decode: assert property (@(A or B or C)
    !$isunknown({A,B,C}) |-> ##0 (! $isunknown(Y) && (Y == (8'h01 << {A,B,C})))
  );

  // One-hot guarantee when inputs are known
  a_onehot: assert property (@(A or B or C)
    !$isunknown({A,B,C}) |-> ##0 $onehot(Y)
  );

  // Optional: outputs not X when inputs are known (redundant with a_decode but explicit)
  a_no_x: assert property (@(A or B or C)
    !$isunknown({A,B,C}) |-> ##0 ! $isunknown(Y)
  );

  // Functional coverage: hit all 8 input combinations with the matching output bit high
  c_000: cover property (@(A or B or C) {A,B,C}==3'b000 ##0 Y[0]);
  c_001: cover property (@(A or B or C) {A,B,C}==3'b001 ##0 Y[1]);
  c_010: cover property (@(A or B or C) {A,B,C}==3'b010 ##0 Y[2]);
  c_011: cover property (@(A or B or C) {A,B,C}==3'b011 ##0 Y[3]);
  c_100: cover property (@(A or B or C) {A,B,C}==3'b100 ##0 Y[4]);
  c_101: cover property (@(A or B or C) {A,B,C}==3'b101 ##0 Y[5]);
  c_110: cover property (@(A or B or C) {A,B,C}==3'b110 ##0 Y[6]);
  c_111: cover property (@(A or B or C) {A,B,C}==3'b111 ##0 Y[7]);

endmodule

// Bind into DUT
bind decoder_3to8 decoder_3to8_sva u_decoder_3to8_sva (.*);