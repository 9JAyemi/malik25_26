
module barrel_shifter (
    input [3:0] A,
    input [1:0] shift_amount, // 2-bit shift amount
    input shift_dir, // 1 for left shift, 0 for right shift
    output reg [3:0] Y
);

always @(*) begin
    if (shift_dir) begin // Left shift
        if (shift_amount == 2'b00) // No shift
            Y = A;
        else if (shift_amount == 2'b01) // Shift by 1
            Y = {A[2:0], 1'b0};
        else if (shift_amount == 2'b10) // Shift by 2
            Y = {A[1:0], 2'b00};
        else // Shift by 3
            Y = {A[0], 3'b000};
    end else begin // Right shift
        if (shift_amount == 2'b00) // No shift
            Y = A;
        else if (shift_amount == 2'b01) // Shift by 1
            Y = {1'b0, A[3:1]};
        else if (shift_amount == 2'b10) // Shift by 2
            Y = {2'b00, A[3:2]};
        else // Shift by 3
            Y = {3'b000, A[3]};
    end
end

endmodule

module decoder (
    input enable,
    input [1:0] select,
    output reg [15:0] out
);

always @(select) begin
    if (enable) begin
        case (select)
            2'b00: out = 16'h0001;
            2'b01: out = 16'h0002;
            2'b10: out = 16'h0004;
            2'b11: out = 16'h0008;
        endcase
    end else begin
        out = 16'b0;
    end
end

endmodule

module top_module (
    input [3:0] A,
    input [1:0] shift_amount,
    input shift_dir,
    input enable,
    input [1:0] select,
    output [15:0] out
);

wire [3:0] shifted_A;
barrel_shifter bs (
    .A(A),
    .shift_amount(shift_amount),
    .shift_dir(shift_dir),
    .Y(shifted_A)
);

wire [15:0] decoder_out;
decoder d (
    .enable(enable),
    .select(select),
    .out(decoder_out)
);

assign out = {16'b0, decoder_out[3:0]} | {shifted_A, 12'b0};

endmodule
