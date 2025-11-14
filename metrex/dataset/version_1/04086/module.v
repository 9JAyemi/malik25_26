
module ALU(input [10:0] OP,
           input [7:0] A,
           input [7:0] B,
           input CI,
           output reg CO,
           output reg VO,
           output reg SO,
           output reg ZO,
           output reg [7:0] Result,
           output reg [7:0] IntR);

  // Declare intermediate wires
  wire [7:0] add_out, sub_out, and_out, or_out, xor_out, inc_out, dec_out, sl_out, sr_out, rl_out, rr_out, slt_out;
  wire [7:0] add_in_b, sub_in_b, sl_in_b, sr_in_b, rl_in_b, rr_in_b;
  wire add_cout, sub_cout, sl_cout, sr_cout;
  
  // Define intermediate logic
  assign add_in_b = B;
  assign sub_in_b = ~B + 1;
  assign sl_in_b = B << 1;
  assign sr_in_b = B >> 1;
  assign rl_in_b = {B[6:0], B[7]};
  assign rr_in_b = {B[0], B[7:1]};
  
  MyAdder adder(.A(A), .B(add_in_b), .CI(CI), .S(add_out), .CO(add_cout));
  MyAdder adder_sub(.A(A), .B(sub_in_b), .CI(CI), .S(sub_out), .CO(sub_cout));
  assign and_out = A & B;
  assign or_out = A | B;
  assign xor_out = A ^ B;
  assign inc_out = A + 1;
  assign dec_out = A - 1;
  assign sl_out = sl_in_b;
  MyAdder shifter_r(.A(A), .B(sr_in_b), .CI(sr_in_b[0]), .S(sr_out), .CO(sr_cout));
  assign rl_out = rl_in_b;
  assign rr_out = rr_in_b;
  assign slt_out = (A < B) ? 1 : 0;
  
  // Select output based on OP
  always @(*) begin
    case (OP)
      11'b00_00_00_000: begin // ADD
        IntR = add_out;
        Result = add_out;
        CO = add_cout;
        VO = (A[7] == B[7] && A[7] != Result[7]) ? 1 : 0;
        SO = Result[7];
        ZO = (Result == 0) ? 1 : 0;
      end
      11'b00_00_00_001: begin // SUB
        IntR = sub_out;
        Result = sub_out;
        CO = sub_cout;
        VO = (A[7] != B[7] && A[7] != Result[7]) ? 1 : 0;
        SO = Result[7];
        ZO = (Result == 0) ? 1 : 0;
      end
      11'b00_00_00_010: begin // AND
        IntR = and_out;
        Result = and_out;
        CO = 1'b0;
        VO = 1'b0;
        SO = Result[7];
        ZO = (Result == 0) ? 1 : 0;
      end
      11'b00_00_00_011: begin // OR
        IntR = or_out;
        Result = or_out;
        CO = 1'b0;
        VO = 1'b0;
        SO = Result[7];
        ZO = (Result == 0) ? 1 : 0;
      end
      11'b00_00_00_100: begin // XOR
        IntR = xor_out;
        Result = xor_out;
        CO = 1'b0;
        VO = 1'b0;
        SO = Result[7];
        ZO = (Result == 0) ? 1 : 0;
      end
      11'b00_00_00_101: begin // INC
        IntR = inc_out;
        Result = inc_out;
        CO = (A == 8'hFF) ? 1 : 0;
        VO = (A[7] == 1 && Result[7] == 0) ? 1 : 0;
        SO = Result[7];
        ZO = (Result == 0) ? 1 : 0;
      end
      11'b00_00_00_110: begin // DEC
        IntR = dec_out;
        Result = dec_out;
        CO = (A == 8'h00) ? 1 : 0;
        VO = (A[7] == 0 && Result[7] == 1) ? 1 : 0;
        SO = Result[7];
        ZO = (Result == 0) ? 1 : 0;
      end
      11'b00_00_00_111: begin // SHL
        IntR = sl_out;
        Result = sl_out;
        CO = A[7];
        VO = (A[7] != Result[7]) ? 1 : 0;
        SO = Result[7];
        ZO = (Result == 0) ? 1 : 0;
      end
      11'b00_00_01_000: begin // SHR
        IntR = sr_out;
        Result = sr_out;
        CO = A[0];
        VO = 1'b0;
        SO = Result[7];
        ZO = (Result == 0) ? 1 : 0;
      end
      11'b00_00_01_001: begin // ROL
        IntR = rl_out;
        Result = rl_out;
        CO = A[7];
        VO = (A[7] != Result[7]) ? 1 : 0;
        SO = Result[7];
        ZO = (Result == 0) ? 1 : 0;
      end
      11'b00_00_01_010: begin // ROR
        IntR = rr_out;
        Result = rr_out;
        CO = A[0];
        VO = (A[0] != Result[0]) ? 1 : 0;
        SO = Result[7];
        ZO = (Result == 0) ? 1 : 0;
      end
      11'b00_00_01_011: begin // SLT
        IntR = slt_out;
        Result = slt_out;
        CO = 1'b0;
        VO = 1'b0;
        SO = Result[7];
        ZO = (Result == 0) ? 1 : 0;
      end
      default: begin // Invalid OP
        IntR = 8'h00;
        Result = 8'h00;
        CO = 1'b0;
        VO = 1'b0;
        SO = 1'b0;
        ZO = 1'b0;
      end
    endcase
  end
endmodule
module MyAdder(input [7:0] A, B, input CI, output [7:0] S, output CO);
  wire [8:0] sum;
  assign sum = A + B + CI;
  assign S = sum[7:0]; // Truncate to 8 bits
  assign CO = sum[8];
endmodule