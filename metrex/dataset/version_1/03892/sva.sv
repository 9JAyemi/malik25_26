// SVA for adder_4bit
module adder_4bit_sva(input logic [3:0] A,
                      input logic [3:0] B,
                      input logic       S,
                      input logic [3:0] C);

  // Functional correctness (mask to 4 bits; allow delta for combinational settle)
  assert property (@(A or B or S)
                   (!$isunknown(S) && (S==1'b0)) |-> ##0 (C == ((A + B) & 4'hF)));

  assert property (@(A or B or S)
                   (!$isunknown(S) && (S==1'b1)) |-> ##0 (C == ((A - B) & 4'hF)));

  // If inputs are known, output must be known (next delta)
  assert property (@(A or B or S)
                   (!$isunknown({A,B,S})) |-> ##0 (!$isunknown(C)));

  // Compact functional coverage
  cover property (@(A or B or S)
                  (!$isunknown({A,B,S})) && (S==1'b0) && (($unsigned(A)+$unsigned(B)) >= 16));

  cover property (@(A or B or S)
                  (!$isunknown({A,B,S})) && (S==1'b1) && (A < B));

  cover property (@(A or B or S)
                  (!$isunknown({A,B,S})) && (S==1'b1) && (A == B));

  cover property (@(A or B or S)
                  (!$isunknown({A,B,S})) && (S==1'b0) && (A==4'hF) && (B==4'hF));

  cover property (@(A or B or S)
                  (!$isunknown({A,B,S})) && (S==1'b0) && (A==4'h0) && (B==4'h0));

  cover property (@(posedge S) !$isunknown({A,B}));
  cover property (@(negedge S) !$isunknown({A,B}));

endmodule

// Bind into DUT
bind adder_4bit adder_4bit_sva u_adder_4bit_sva (.A(A), .B(B), .S(S), .C(C));