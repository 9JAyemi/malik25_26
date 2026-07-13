module full_adder_4bit #(parameter DW = 4 // data width
                         )
  ( input [DW-1:0]  A, //input A
    input [DW-1:0]  B, //input B
    input [DW-1:0]  C_in, //input C_in
    output [DW-1:0] S, //sum output
    output [DW-1:0] C_out //carry output
  );

  `ifdef CFG_ASIC
    genvar i;
    for (i = 0; i < DW; i = i + 1) begin
      asic_csa32 asic_csa32 (.s(S[i]), .c(C_out[i]), .in2(C_in[i]), .in1(B[i]), .in0(A[i]));
    end
  `else
    assign S[DW-1:0] = A[DW-1:0] ^ B[DW-1:0] ^ C_in[DW-1:0];
    assign C_out[DW-1:0] = (A[DW-1:0] & B[DW-1:0]) | (B[DW-1:0] & C_in[DW-1:0]) | (C_in[DW-1:0] & A[DW-1:0]);
  `endif // !`ifdef CFG_ASIC

endmodule