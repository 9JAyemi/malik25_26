module top_module (
    input [3:0] multiplier,
    input [3:0] multiplicand,
    input [15:0] in0,
    input [15:0] in1,
    input ctrl,
    output reg [15:0] out
);

    wire [7:0] unsigned_mult_out;
    wire [3:0] add_sub_out;
    wire [15:0] final_out;

    unsigned_multiplier unsigned_mult(.a(multiplier), .b(multiplicand), .p(unsigned_mult_out));
    add_sub add_sub(.a(multiplier), .b(multiplicand), .ctrl(ctrl), .s(add_sub_out));
    functional_module functional(.in0(unsigned_mult_out), .in1(add_sub_out), .out(final_out));

    always @(*) begin
        if (ctrl == 0) begin
            out = final_out;
        end else begin
            out = final_out + in0 + in1;
        end
    end

endmodule

module unsigned_multiplier (
    input [3:0] a,
    input [3:0] b,
    output reg [7:0] p
);

    always @(*) begin
        p = a * b;
    end

endmodule

module add_sub (
    input [3:0] a,
    input [3:0] b,
    input ctrl,
    output reg [3:0] s
);

    always @(*) begin
        if (ctrl == 0) begin
            s = a + b;
        end else begin
            s = a - b;
        end
    end

endmodule

module functional_module (
    input [7:0] in0,
    input [3:0] in1,
    output reg [15:0] out
);

    always @(*) begin
        out = {8'b0, in0} + {12'b0, in1};
    end

endmodule