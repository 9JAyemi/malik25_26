module left_rotation(
    output reg [31:0] o,
    input [31:0] i,
    input [4:0] n
);

always @(*) begin
    o = {i[(n+31):0], i[31:(n+1)]};
end

endmodule