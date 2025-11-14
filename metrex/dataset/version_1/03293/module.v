
module top_module (
    input [15:0] A,
    input [15:0] B,
    input [3:0] control,
    output reg [15:0] result,
    output reg valid
);

    wire [15:0] shifted_data;
    wire [3:0] alu_result;
    wire [15:0] and_result;

    // Instantiate barrel shifter module
    barrel_shifter_16bit shifter(
        .data_in(A),
        .shift_amount(control[2:0]),
        .mode(control[3]),
        .shifted_out(shifted_data)
    );

    // Instantiate ALU module
    alu alu_inst(
        .A(B[3:0]),
        .B(B[7:4]),
        .op(control[1:0]),
        .result(alu_result),
        .valid(valid)
    );

    // Perform bitwise AND operation on shifted data and ALU result
    assign and_result = shifted_data & alu_result;

    // Assign result output
    always @(*) begin
        case(control[3:0])
            4'b0000: result = A; // Pass through A
            4'b0001: result = B; // Pass through B
            4'b0010: result = A + B; // Add A and B
            4'b0011: result = A - B; // Subtract B from A
            4'b0100: result = shifted_data; // Output shifted data
            4'b0101: result = alu_result; // Output ALU result
            4'b0110: result = A & B; // Bitwise AND of A and B
            4'b0111: result = A | B; // Bitwise OR of A and B
            4'b1000: result = and_result; // Output AND result
            default: result = 16'h0000; // Default to 0
        endcase
    end

endmodule
module barrel_shifter_16bit (
    input [15:0] data_in,
    input [2:0] shift_amount,
    input mode,
    output [15:0] shifted_out
);
    reg [15:0] shifted_data;

    always @(*) begin
        case(shift_amount)
            3'b000: shifted_data = data_in; // No shift
            3'b001: shifted_data = data_in << 1; // Shift left by 1
            3'b010: shifted_data = data_in << 2; // Shift left by 2
            3'b011: shifted_data = data_in << 3; // Shift left by 3
            3'b100: shifted_data = data_in << 4; // Shift left by 4
            3'b101: shifted_data = data_in << 5; // Shift left by 5
            3'b110: shifted_data = data_in << 6; // Shift left by 6
            3'b111: shifted_data = data_in << 7; // Shift left by 7
            default: shifted_data = data_in; // Default to original data
        endcase
    end

    assign shifted_out = mode ? shifted_data : data_in; // Output shifted data or original data based on mode input

endmodule
module alu (
    input [3:0] A,
    input [3:0] B,
    input [1:0] op,
    output reg [3:0] result,
    output reg valid
);
    always @(*) begin
        case(op)
            2'b00: result = A & B; // Bitwise AND
            2'b01: result = A | B; // Bitwise OR
            2'b10: result = A + B; // Addition
            2'b11: result = A - B; // Subtraction
            default: result = 4'h0; // Default to 0
        endcase
        valid = 1; // Output is always valid
    end

endmodule