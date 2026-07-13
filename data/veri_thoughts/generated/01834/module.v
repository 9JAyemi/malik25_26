
module LOA #(parameter LPL=10, parameter W=16)(
    input wire [W - 1:0] in1,
    input wire [W - 1:0] in2,
    output wire [W:0] res
    );

wire [LPL-1:0] in1LowerPart;
wire [LPL-1:0] in2LowerPart;
wire [W-LPL-1:0] in1UpperPart;
wire [W-LPL-1:0] in2UpperPart;
wire [W-LPL:0] midRes;
wire [LPL-1:0] ORLowerPart;
wire ANDN;

assign ORLowerPart = ((in1[LPL-1:0]) |( in2[LPL-1:0]));
and and_1(ANDN,in1[LPL-1],in2[LPL-1]);
assign  midRes= in1[W-1:LPL] + in2[W-1:LPL] + ANDN;
assign res = {midRes, ORLowerPart};

endmodule
