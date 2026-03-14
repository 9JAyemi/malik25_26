module d_ff (
    input clk,
    input reset,
    input d,
    output reg q,
    output reg q_n
);

    always @(posedge clk or negedge reset) begin
        if (~reset) begin
            q <= 1'b0;
        end else begin
            q <= d;
        end
    end

    always @(*) begin
        q_n = ~q;
    end

endmodule