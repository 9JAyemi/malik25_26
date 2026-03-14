module d_ff_async_reset_set (
    input clk,
    input d,
    input reset,
    input set,
    output reg q,
    output reg q_n
);

    always @(posedge clk) begin
        if (reset) begin
            q <= 1'b0;
            q_n <= 1'b1;
        end else if (set) begin
            q <= 1'b1;
            q_n <= 1'b0;
        end else begin
            q <= d;
            q_n <= ~d;
        end
    end

endmodule