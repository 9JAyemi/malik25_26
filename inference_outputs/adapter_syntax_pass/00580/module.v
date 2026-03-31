
module binary_subtractor_32bit (
    input [31:0] A,
    input [31:0] B,
    output reg [31:0] S
);

wire [31:0] B_comp;

complement_2_32bit comp_inst (
    .A(B),
    .S(B_comp)
);

always @(*) begin
    S <= A + B_comp;
end

endmodule

module complement_2_32bit (
    input [31:0] A,
    output reg [31:0] S
);

always @(*) begin
    S <= ~A + 1;
end

endmodule
