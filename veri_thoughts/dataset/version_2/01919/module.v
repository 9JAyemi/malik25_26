
module register (
    input d,
    input clk,
    input ena,
    input clr,
    input pr,
    output reg q
);

always @(posedge clk) begin
    if (clr) begin
        q <= 1'b0;
    end else if (pr) begin
        q <= 1'b1;
    end else if (ena) begin
        q <= d;
    end
end

endmodule