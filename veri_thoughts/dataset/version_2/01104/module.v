
module final_output (
    input clk,
    input reset,
    input d,
    input rise,
    input down,
    output q_out
);

reg q = 0;
always @(posedge clk) begin
    if (reset) begin
        q <= 0;
    end else begin
        if (rise) begin
            q <= 1;
        end else if (down) begin
            q <= 0;
        end
    end
end

assign q_out = q;

endmodule