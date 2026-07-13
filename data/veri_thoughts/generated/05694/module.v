
module boolean_ops (
   // Outputs
   logic_out, 
   // Inputs
   rs1_data, rs2_data, isand, isor, isxor, pass_rs2_data, inv_logic, 
   ifu_exu_sethi_inst_e
   );

   input [63:0] rs1_data;             // 1st input operand
   input [63:0] rs2_data;             // 2nd input operand
   input isand;
   input isor;
   input isxor;
   input pass_rs2_data;
   input inv_logic;
   input ifu_exu_sethi_inst_e;       // zero out top half of rs2 on mov

   output [63:0] logic_out;      // output of logic block

   wire [63:0] rs1_data_bf1;                 // buffered rs1_data
   wire [63:0] rs2_data_bf1;                 // buffered rs2_data
   wire [63:0] mov_data;
   wire [63:0] result_and;              // rs1_data & rs2_data
   wire [63:0] result_or;               // rs1_data | rs2_data
   wire [63:0] result_xor;              // rs1_data ^ rs2_data
   wire [63:0] rs2_xor_invert;           // output of mux between various results

   // buffer inputs
   assign rs1_data_bf1 = rs1_data;
   assign rs2_data_bf1 = rs2_data;

   // zero out top of rs2 for sethi_inst
   assign mov_data[63:32] = rs2_data_bf1[63:32] & {32{~ifu_exu_sethi_inst_e}};
   assign mov_data[31:0] = rs2_data_bf1[31:0];

   // invert input2 for andn, orn, xnor
   assign rs2_xor_invert = rs2_data_bf1 ^ {64{inv_logic}};

   // do boolean ops
   assign result_and = rs1_data_bf1 & rs2_xor_invert;
   assign result_or = rs1_data_bf1 | rs2_xor_invert;
   assign result_xor = rs1_data_bf1 ^ rs2_xor_invert;

   // mux between various results
   assign logic_out = (isand) ? result_and: 
                        (isor) ? result_or:
                        (isxor) ? result_xor:
                        mov_data;

endmodule
