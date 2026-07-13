
module arithmetic_right_shift (
    input clk,
    input reset,
    input [3:0] A,
    input [1:0] shift_amount,
    output reg [3:0] Q
);

always @(posedge clk, negedge reset) begin
    if (!reset) begin
        Q <= 4'b0000;
    end else begin
        case (shift_amount)
            2'b00: Q <= A;
            2'b01: Q <= {A[2:0], A[3]};
            2'b10: Q <= {A[3], A[3:1]};
            2'b11: Q <= {A[2:0], A[3]};
        endcase
    end
end

endmodule

module barrel_shifter (
    input clk,
    input reset,
    input [3:0] A,
    input [1:0] shift,
    input [3:0] shift_data,
    output reg [3:0] Q
);

always @(posedge clk, negedge reset) begin
    if (!reset) begin
        Q <= 4'b0000;
    end else begin
        case (shift)
            2'b00: Q <= A;
            2'b01: Q <= {A[2:0], shift_data[3]};
            2'b10: Q <= {shift_data[0], A[3:1]};
            2'b11: Q <= {A[2:0], A[3]};
        endcase
    end
end

endmodule

module functional_module (
    input [3:0] shift_output,
    input [3:0] barrel_output,
    output wire [3:0] result
);

assign result = shift_output + barrel_output;

endmodule

module top_module (
    input clk,
    input reset,
    input [3:0] A,
    input [1:0] shift,
    input [1:0] shift_amount,
    input select,
    output [3:0] Q
);

wire [3:0] shift_output;
wire [3:0] barrel_output;
wire [3:0] result;

arithmetic_right_shift ars (
    .clk(clk),
    .reset(reset),
    .A(A),
    .shift_amount(shift_amount),
    .Q(shift_output)
);

barrel_shifter bs (
    .clk(clk),
    .reset(reset),
    .A(A),
    .shift(shift),
    .shift_data(shift_output),
    .Q(barrel_output)
);

functional_module fm (
    .shift_output(shift_output),
    .barrel_output(barrel_output),
    .result(result)
);

assign Q = select ? barrel_output : shift_output;

endmodule
