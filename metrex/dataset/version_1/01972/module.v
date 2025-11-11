
module top_module(
    input clk,
    input load,
    input [1:0] ena,
    input [99:0] in,
    output [7:0] q
);

    wire [99:0] rotated_data;
    wire [2:0] comb_out;
    wire [7:0] final_out;

    rotator rotator_inst(
        .clk(clk),
        .load(load),
        .ena(ena),
        .data(in),
        .rotated_data(rotated_data)
    );

    combinational combinational_inst(
        .in(rotated_data),
        .out(comb_out)
    );

    final_module final_inst(
        .in1(rotated_data[7:0]),
        .in2(comb_out),
        .out(final_out)
    );

    assign q = final_out;

endmodule
module rotator(
    input clk,
    input load,
    input [1:0] ena,
    input [99:0] data,
    output [99:0] rotated_data
);

    reg [99:0] shift_reg;

    always @(posedge clk) begin
        if (load) begin
            shift_reg <= data;
        end else begin
            if (ena[0]) begin
                shift_reg <= {shift_reg[98:0], shift_reg[99]};
            end else if (ena[1]) begin
                shift_reg <= {shift_reg[1:99], shift_reg[0]};
            end
        end
    end

    assign rotated_data = shift_reg;

endmodule
module combinational(
    input [99:0] in,
    output [2:0] out
);

    assign out[0] = &in;
    assign out[1] = |in;
    assign out[2] = ^in;

endmodule
module final_module(
    input [7:0] in1,
    input [2:0] in2,
    output [7:0] out
);

    reg [7:0] out;

    always @(*) begin
        case (in2)
            3'b000: out = in1 & 8'hFF;
            3'b001: out = in1 | 8'hFF;
            3'b010: out = in1 ^ 8'hFF;
            3'b011: out = in1 + 8'h01;
            3'b100: out = in1 - 8'h01;
            default: out = 8'h00;
        endcase
    end

endmodule