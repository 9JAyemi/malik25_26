module dff_async_reset (
    q,
    d,
    clk,
    reset
);

    output q;
    input d, clk, reset;

    reg q;

    always @(posedge clk or negedge reset) begin
        if (~reset) begin
            q <= 0;
        end else begin
            q <= d;
        end
    end

endmodule
