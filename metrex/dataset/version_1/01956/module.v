module shift_register (
    input [15:0] D,
    input SH,
    input LD,
    input clk,
    output reg [15:0] Q
);

reg [15:0] Q1, Q2;

always @ (posedge clk) begin
    if (LD) begin
        Q1 <= D;
    end else begin
        Q1 <= Q2;
    end
end

always @ (posedge clk) begin
    if (SH) begin
        Q2 <= {Q1[14:0], 1'b0};
    end else begin
        Q2 <= {1'b0, Q1[15:1]};
    end
end

always @* begin
    Q = Q2;
end

endmodule