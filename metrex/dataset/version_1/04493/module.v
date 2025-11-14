
module Mux12(A, B, C, D, S0, S1, O);
  input [11:0] A, B, C, D;
  input S0, S1;
  output [11:0] O;
  
  wire [11:0] AB, CD;
  wire sel;
  
  assign sel = S1 ? S0 : ~S0;
  
  generate
    genvar i;
    for (i = 0; i < 12; i = i + 1) begin
      assign AB[i] = S0 ? A[i] : B[i];
      assign CD[i] = S0 ? C[i] : D[i];
    end
  endgenerate
  
  assign O = sel ? AB : CD;
  
endmodule