module ripple_carry_adder (
    input [3:0] A,
    input [3:0] B,
    output reg [3:0] OUT
);

    always @(*) begin
        OUT = A + B;
    end

endmodule

module barrel_shifter (
    input [15:0] data,
    input [3:0] shift_amount,
    input direction,
    output reg [15:0] q
);

    always @(*) begin
        if (direction == 1'b0) begin // shift left
            q = data << shift_amount;
        end else begin // shift right
            q = data >> shift_amount;
        end
    end

endmodule

module top_module (
    input [3:0] A,
    input [3:0] B,
    input [15:0] data,
    input [3:0] shift_amount,
    input direction,
    output reg [15:0] q
);

    wire [3:0] adder_out;
    wire [15:0] shifted_data;

    ripple_carry_adder adder_inst (
        .A(A),
        .B(B),
        .OUT(adder_out)
    );

    barrel_shifter shifter_inst (
        .data(data),
        .shift_amount(shift_amount),
        .direction(direction),
        .q(shifted_data)
    );

    always @(*) begin
        q = adder_out + shifted_data;
    end

endmodule