// SVA for comparator
// Bind into DUT to keep assertions separate
module comparator_sva (input logic [1:0] A, B, input logic EQ);

  // Core functional check (combinational, zero-time update, known inputs)
  // On any A/B/EQ activity, after delta, EQ must reflect (A == B)
  assert property (@(A or B or EQ)
                   !$isunknown({A,B}) |-> ##0 (EQ == (A == B)))
    else $error("EQ mismatch with A==B");

  // No X/Z on EQ when inputs are known
  assert property (@(A or B)
                   !$isunknown({A,B}) |-> ##0 !$isunknown(EQ))
    else $error("EQ has X/Z with known inputs");

  // Functional coverage: all input combinations reached and EQ correct
  genvar i,j;
  generate
    for (i=0; i<4; i++) begin : GA
      localparam logic [1:0] LA = i[1:0];
      for (j=0; j<4; j++) begin : GB
        localparam logic [1:0] LB = j[1:0];
        cover property (@(A or B)
                        !$isunknown({A,B}) &&
                        (A == LA) && (B == LB) ##0 (EQ == (LA == LB)));
      end
    end
  endgenerate

  // Edge coverage on EQ
  cover property (@(A or B or EQ) $rose(EQ));
  cover property (@(A or B or EQ) $fell(EQ));

endmodule

bind comparator comparator_sva u_comparator_sva (.A(A), .B(B), .EQ(EQ));