
module mod_add16(
    input  [3:0] a,
    input  [3:0] b,
    input  rst,
    input  clk,
    output  [3:0] out
);

    reg [3:0] out;

    always @(posedge clk or posedge rst) begin
        if (rst) begin
            out <= 4'b0;
        end else begin
            out <= (a + b) % 16;
            if (out >= 16) begin
                out <= out - 16;
            end
        end
    end

endmodule