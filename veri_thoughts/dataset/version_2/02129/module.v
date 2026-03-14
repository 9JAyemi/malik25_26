module d_ff_clear_preset (
    input clk,
    input d,
    input clr,
    input preset,
    output reg q,
    output reg q_n
);

    always @(posedge clk) begin
        if (clr) begin
            q <= 0;
            q_n <= 1;
        end else if (preset) begin
            q <= 1;
            q_n <= 0;
        end else begin
            q <= d;
            q_n <= ~d;
        end
    end

endmodule