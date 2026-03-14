
module top_module(
    input [3:0] in,
    input [2:0] sel,
    output [1:0] out
);

wire [1:0] level1 [0:3];
wire level2 [0:1];
wire level3;
wire level4;
wire level5;

assign level1[0] = {1'b0, in[1]};
assign level1[1] = {1'b0, in[3]};
assign level1[2] = {in[2], in[1]}; // Corrected the bounds of the range
assign level1[3] = {in[3], in[2]}; // Corrected the bounds of the range

priority_encoder pe1(
    .in(level1[0]), 
    .out(level2[0])
);

priority_encoder pe2(
    .in(level1[1]), 
    .out(level2[1])
);

priority_encoder pe3(
    .in(level1[2]), 
    .out(level3)
);

priority_encoder pe4(
    .in(level1[3]), 
    .out(level4)
);

assign level5 = (level2[1] == 1'b1) ? 1'b1 :
             (level2[0] == 1'b1) ? 1'b0 : // Corrected the precedence of operators
             1'b0;

assign out = (sel == 3'b000) ? level1[0] :
             (sel == 3'b001) ? level2[0] :
             (sel == 3'b010) ? level3 :
             (sel == 3'b011) ? level4 :
             (sel == 3'b100) ? level5 : 2'bxx;

endmodule
module priority_encoder(
    input [1:0] in,
    output out
);

assign out = (in[1] == 1'b1) ? 1'b1 :
             (in[0] == 1'b1) ? 1'b0 :
             1'b0;

endmodule