module alu_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [2:0] opcode,
    output logic [3:0] out,
    output logic zero
);
    // Combinational logic, so use @(posedge clk)
    // Check if the output is correct based on the opcode
    check_output: assert property (
        @(posedge clk) disable iff (!reset) (opcode == 3'b000) |-> (out == A + B)
    );
    check_output_1: assert property (
        @(posedge clk) disable iff (!reset) (opcode == 3'b001) |-> (out == A - B)
    );
    check_output_2: assert property (
        @(posedge clk) disable iff (!reset) (opcode == 3'b010) |-> (out == A & B)
    );
    check_output_3: assert property (
        @(posedge clk) disable iff (!reset) (opcode == 3'b011) |-> (out == A | B)
    );
    check_output_4: assert property (
        @(posedge clk) disable iff (!reset) (opcode == 3'b100) |-> (out == A ^ B)
    );
    check_output_5: assert property (
        @(posedge clk) disable iff (!reset) (opcode == 3'b101) |-> (out == A << 1)
    );
    check_output_6: assert property (
        @(posedge clk) disable iff (!reset) (opcode == 3'b110) |-> (out == A >> 1)
    );
    check_output_7: assert property (
        @(posedge clk) disable iff (!reset) (opcode == 3'b111) |-> (out == ~A)
    );
    
    // Check if the zero flag is set correctly
    check_zero_flag: assert property (
        @(posedge clk) disable iff (!reset) (out == 4'b0000) |-> (zero == 1'b1)
    );
    check_zero_flag_1: assert property (
        @(posedge clk) disable iff (!reset) (out != 4'b0000) |-> (zero == 1'b0)
    );
endmodule