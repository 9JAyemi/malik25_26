module v0dbcb9_v9a2a06 (
    output reg o1,
    output reg o0,
    input [1:0] i
);

always @(*) begin
    case (i)
        2'b00 : begin
            o1 = 1'b0;
            o0 = 1'b1;
        end
        2'b01 : begin
            o1 = 1'b1;
            o0 = 1'b0;
        end
        2'b10 : begin
            o1 = 1'b0;
            o0 = 1'b0;
        end
        2'b11 : begin
            o1 = 1'b1;
            o0 = 1'b1;
        end
    endcase
end

endmodule

module v0dbcb9 (
    input [1:0] v8b19dd,
    output v3f8943,
    output v64d863
);

wire w0;
wire w1;
wire [0:1] w2;

assign v3f8943 = w0;
assign v64d863 = w1;
assign w2 = v8b19dd;

v0dbcb9_v9a2a06 v9a2a06 (
    .o1(w0),
    .o0(w1),
    .i(w2)
);

endmodule