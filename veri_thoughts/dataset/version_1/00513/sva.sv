// SVA for comparator_4bit
module comparator_4bit_sva(input logic [3:0] A, B,
                           input logic [1:0] result);

  // Event-based sampling for combinational checks
  default clocking cb @ (A or B or result); endclocking

  // Always-on structural/encoding checks
  assert property (! $isunknown(result)) else $error("result has X/Z");
  assert property (result inside {2'b00,2'b01,2'b10})
    else $error("Illegal result code (11)");

  // Functional checks only when inputs are known
  default disable iff ($isunknown({A,B}));

  // Correct encoding vs arithmetic compare
  assert property ( (result==2'b01) == (A > B) );
  assert property ( (result==2'b10) == (A < B) );
  assert property ( (result==2'b00) == (A == B) );

  // MSB-different shortcut honored
  assert property ( (A[3]^B[3]) |-> (result == (A[3] ? 2'b01 : 2'b10)) );

  // Coverage: all relations and key corners
  cover property (A > B && result==2'b01);
  cover property (A < B && result==2'b10);
  cover property (A == B && result==2'b00);

  cover property (A[3] && !B[3] && result==2'b01);
  cover property (!A[3] && B[3] && result==2'b10);

  cover property (A==4'h0 && B==4'h0 && result==2'b00);
  cover property (A==4'hF && B==4'hF && result==2'b00);
  cover property (A==4'hF && B==4'h0 && result==2'b01);
  cover property (A==4'h0 && B==4'hF && result==2'b10);

endmodule

// Bind into DUT
bind comparator_4bit comparator_4bit_sva sva_inst(.A(A), .B(B), .result(result));