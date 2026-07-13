
module top_module (
    input  [31:0] a,
    input  [31:0] b,
    input         select, //Select input to choose between adder and multiplexer
    output [31:0] sum
); 

wire [31:0] adder_out;
wire  mux_out;

adder adder_inst (
    .a(a),
    .b(b),
    .sum(adder_out)
);

mux mux_inst (
    .a(a),
    .b(b),
    .c(select),
    .w(mux_out)
);

assign sum = (select == 1'b1) ? adder_out : {31'b0, mux_out};

endmodule
module adder (
    input  [31:0] a,
    input  [31:0] b,
    output [31:0] sum
);

genvar i;

generate
    for (i = 0; i < 32; i = i + 1) begin : adder_loop
        full_adder full_adder_inst (
            .a(a[i]),
            .b(b[i]),
            .cin(0), //Assuming there is no carry in
            .sum(sum[i])
        );
    end
endgenerate

endmodule
module mux (
    input [31:0] a,
    input [31:0] b,
    input c,
    output w
);

assign w = c ? b[0] : a[0];

endmodule
module full_adder (
    input a, b, cin,
    output sum, cout
);

assign sum = a ^ b ^ cin;
assign cout = (a & b) | (b & cin) | (a & cin);

endmodule