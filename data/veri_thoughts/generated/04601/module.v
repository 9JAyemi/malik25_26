module top_module(
    input [15:0] a,
    input [15:0] b,
    input select,
    output [31:0] sum
);

    wire [15:0] adder1_out;
    wire [15:0] adder2_out;
    wire [15:0] carry_select_out;

    // Instantiate the two 16-bit adders
    adder16bit adder1(.a(a), .b(b), .sum(adder1_out));
    adder16bit adder2(.a(a), .b(b), .sum(adder2_out));

    // Instantiate the carry select adder
    carry_select_adder csa(.a(adder1_out), .b(adder2_out), .cin(select), .sum(carry_select_out));

    // Control logic to select between the two 16-bit adders
    assign sum = select ? carry_select_out : {16'b0, adder1_out};

endmodule

// 16-bit adder module
module adder16bit(
    input [15:0] a,
    input [15:0] b,
    output [15:0] sum
);

    assign sum = a + b;

endmodule

// Carry select adder module
module carry_select_adder(
    input [15:0] a,
    input [15:0] b,
    input cin,
    output [15:0] sum
);

    wire [15:0] p;
    wire [15:0] g;
    wire [15:0] c;

    assign p = a + b;
    assign g = a & b;
    assign c[0] = cin;

    genvar i;
    generate
        for (i = 1; i < 16; i = i + 1) begin : carry_select_loop
            assign c[i] = (g[i-1] | (p[i-1] & c[i-1]));
        end
    endgenerate

    assign sum = {c[15], p[15:0]};

endmodule