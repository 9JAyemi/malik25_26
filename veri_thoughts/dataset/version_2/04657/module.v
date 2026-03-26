module hw2_B (
    input in,
    input clk,
    input rst_n,
    output reg out
    );

    always @(posedge clk, negedge rst_n) begin
        if (~rst_n) begin
            out <= 1'b0;
        end else begin
            out <= in;
        end
    end

endmodule