module AdderSubtractor (
    input [3:0] A,
    input [3:0] B,
    input Sub,
    output [3:0] S,
    output Cout
);

wire [3:0] A_comp;
wire [3:0] B_comp;

assign A_comp = ~A + 1;
assign B_comp = ~B + 1;

wire [4:0] temp_sum;
assign temp_sum = (Sub == 1) ? A + B_comp : A + B;

assign Cout = (Sub == 1) ? (A >= B) : (temp_sum[4] == 1);
assign S = (Sub == 1) ? temp_sum : temp_sum[3:0];

endmodule

