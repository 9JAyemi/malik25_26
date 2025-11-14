module top_module(
    input [15:0] a,
    input [15:0] b,
    input sub,
    input control,
    output reg [15:0] out
);

    wire [15:0] add_out;
    wire [15:0] sub_out;
    wire carry_out;

    ripple_carry_adder adder(
        .a(a),
        .b(b),
        .carry_in(sub),
        .sum(add_out),
        .carry_out(carry_out)
    );

    xor_gate xor_gate_inst(
        .a(b),
        .b({16{sub}}),
        .out(sub_out)
    );

    always @* begin
        if(control) begin
            out <= add_out;
        end else begin
            out <= sub_out;
        end
    end

endmodule

module ripple_carry_adder(
    input [15:0] a,
    input [15:0] b,
    input carry_in,
    output [15:0] sum,
    output carry_out
);

    genvar i;
    wire [16:0] carry;

    assign carry[0] = carry_in;

    generate
        for(i = 0; i < 16; i = i + 1) begin: loop
            full_adder adder(
                .a(a[i]),
                .b(b[i]),
                .carry_in(carry[i]),
                .sum(sum[i]),
                .carry_out(carry[i+1])
            );
        end
    endgenerate

    assign carry_out = carry[16];

endmodule

module full_adder(
    input a,
    input b,
    input carry_in,
    output sum,
    output carry_out
);

    assign sum = a ^ b ^ carry_in;
    assign carry_out = (a & b) | (carry_in & (a ^ b));

endmodule

module xor_gate(
    input [15:0] a,
    input [15:0] b,
    output [15:0] out
);

    assign out = a ^ b;

endmodule