module barrel_shifter(
    input [7:0] in,
    input [2:0] shift,
    output [7:0] out
);

wire [7:0] shifted;

assign shifted = (shift[2]) ? 8'b0 : (shift[1]) ? {in[0], in[7:1]} : (shift[0]) ? {in[1:0], in[7:2]} : {in[2:0], in[7:3]};

assign out = shifted;

endmodule


module binary_tree_adder(
    input [7:0] in,
    output [7:0] out
);

wire [7:0] sum;

assign sum[0] = in[0];

assign sum[1] = in[0] + in[1];

assign sum[2] = in[2] + in[3];

assign sum[3] = in[0] + in[1] + in[2] + in[3];

assign sum[4] = in[4] + in[5];

assign sum[5] = in[4] + in[5] + in[6] + in[7];

assign sum[6] = in[0] + in[1] + in[2] + in[3] + in[4] + in[5] + in[6] + in[7];

assign out = sum[6];

endmodule


module addictive_control_logic(
    input [7:0] in,
    input select,
    output [7:0] out
);

wire [7:0] shifted;
wire [7:0] sum;

barrel_shifter bs(
    .in(in),
    .shift({select, 2'b00}),
    .out(shifted)
);

binary_tree_adder bta(
    .in(in),
    .out(sum)
);

assign out = (select) ? sum : shifted;

endmodule


module top_module( 
    input [7:0] in,
    input select,
    output [7:0] out
);

addictive_control_logic acl(
    .in(in),
    .select(select),
    .out(out)
);

endmodule