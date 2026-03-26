module DFlipFlop(
    input clk,
    input reset,
    input d,
    output reg q
    );

    always @(posedge clk, negedge reset) begin
        if (!reset) begin
            q <= 1'b0;
        end else begin
            q <= d;
        end
    end

endmodule