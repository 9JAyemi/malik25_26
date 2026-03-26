module binary_counter (
    input clk,
    input rst,
    output reg [3:0] q
);

    always @(posedge clk or negedge rst) begin
        if (~rst) begin
            q <= 4'b0;
        end else begin
            q <= q + 1;
        end
    end

endmodule