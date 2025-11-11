module calculator(
    input [7:0] a,
    input [7:0] b,
    input [1:0] op,
    input [3:0] sel,
    output reg [7:0] out,
    output reg overflow
);

wire [7:0] a_mag, b_mag; // Removed 'add_result' as it is a wire and cannot be assigned to
reg [7:0] add_result; // Declared 'add_result' as a reg since it is assigned to

reg [1:0] op_sel;

// Convert a and b to sign-magnitude format
assign a_mag = (a[7] == 1) ? {1'b0, ~a[7:0] + 1'b1} : a;
assign b_mag = (b[7] == 1) ? {1'b0, ~b[7:0] + 1'b1} : b;

// Select operation based on op input
always @(op, sel) begin
    case (sel)
        2'b00: op_sel = op; // Output result of selected operation
        2'b01: op_sel = 2'b00; // Addition
        2'b10: op_sel = 2'b01; // Subtraction
        2'b11: op_sel = 2'b10; // Multiplication
        default: op_sel = 2'b11; // Division
    endcase
end

// Perform selected operation using 8-bit adder
always @(a_mag, b_mag, op_sel) begin
    case (op_sel)
        2'b00: add_result = a_mag + b_mag; // Addition
        2'b01: add_result = a_mag - b_mag; // Subtraction
        2'b10: add_result = a_mag * b_mag; // Multiplication
        2'b11: add_result = a_mag / b_mag; // Division
    endcase
end

// Check for signed overflow
always @(add_result) begin
    if (add_result[7] != add_result[6]) begin
        overflow = 1'b1;
    end else begin
        overflow = 1'b0;
    end
end

// Output result of selected operation or previous operation
always @(op_sel, add_result) begin
    if (sel < 4'd4) begin
        out = add_result;
    end else begin
        out = out;
    end
end

endmodule