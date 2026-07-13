
module top_module (
    input  [31:0] a,
    input  [31:0] b,
    input         select, //Select input to choose between adder and multiplexer
    output [31:0] result
);

wire [1:0] sub_out;
wire [0:0] mux_out;
wire [31:0] final_out;

subtractor sub(
    .a(a),
    .b(b),
    .result(sub_out)
);

mux mux_inst(
    .a(a[0]),
    .b(b[0]),
    .c(a[1]),
    .d(b[1]),
    .out(mux_out) //Selecting only the LSBs of a and b
);

final_output final_inst(
    .sub_out(sub_out),
    .select(select),
    .a(a[0]),
    .b(b[0]),
    .c(32'h0),
    .d(32'h0),
    .final_out(final_out)
);

assign result = select ? {31'b0, mux_out} : final_out;

endmodule
module subtractor (
    input  [31:0] a,
    input  [31:0] b,
    output [1:0] result
);

wire [31:0] a_inv;
wire [31:0] b_inv;
wire [31:0] carry_in;
wire [31:0] carry_out;
wire [31:0] sum;

assign a_inv = ~a;
assign b_inv = ~b;

//Generate carry select signals
assign carry_in[0] = 1'b0;
genvar i;
generate
    for (i = 1; i < 32; i = i + 1) begin : carry_select
        assign carry_in[i] = (a[i-1] & b[i-1]) | (a[i-1] & carry_out[i-1]) | (b[i-1] & carry_out[i-1]);
    end
endgenerate

//Generate sum signals
assign sum[0] = a[0] ^ b[0] ^ carry_in[0];
generate
    for (i = 1; i < 32; i = i + 1) begin : sum_gen
        assign sum[i] = a[i] ^ b[i] ^ carry_in[i];
    end
endgenerate

//Generate carry out signal
assign carry_out[0] = (a[0] & b[0]) | (a[0] & carry_in[0]) | (b[0] & carry_in[0]);
generate
    for (i = 1; i < 32; i = i + 1) begin : carry_out_gen
        assign carry_out[i] = (a[i] & b[i]) | (a[i] & carry_out[i-1]) | (b[i] & carry_out[i-1]);
    end
endgenerate

assign result = sum[1:0];

endmodule
module mux (
    input  a,
    input  b,
    input  c,
    input  d,
    output out
);

assign out = (a & ~b & ~c & ~d) | (~a & b & ~c & ~d);

endmodule
module final_output (
    input  [1:0] sub_out,
    input         select,
    input  a,
    input  b,
    input  c,
    input  d,
    output [31:0] final_out
);

assign final_out = select ? {31'b0, (a & ~b & ~c & ~d) | (~a & b & ~c & ~d)} : {31'b0, sub_out};

endmodule