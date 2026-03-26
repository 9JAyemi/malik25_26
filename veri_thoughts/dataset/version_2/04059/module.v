module dff_sr (
    input clk,
    input d,
    input set,
    input reset,
    output reg q,
    output reg q_n
);

always @(posedge clk) begin
    if (reset) begin
        q <= 0;
        q_n <= 1;
    end else if (set) begin
        q <= 1;
        q_n <= 0;
    end else begin
        q <= d;
        q_n <= ~d;
    end
end

endmodule