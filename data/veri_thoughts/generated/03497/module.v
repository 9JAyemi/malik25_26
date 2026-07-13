module binary_counter(
    input [3:0] in,
    output reg [3:0] out,
    output reg overflow
);

always @* begin
    if (in == 4'b1111) begin
        out = 4'b0000;
        overflow = 1;
    end
    else begin
        out = in + 4'b0001;
        overflow = 0;
    end
end

endmodule