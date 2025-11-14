module dff_rst_set (
    input clk,
    input rst,
    input set,
    input d,
    output q,
    output qn
);

reg q;

always @(posedge clk) begin
    if (rst) begin
        q <= 0;
    end
    else if (set) begin
        q <= 1;
    end
    else begin
        q <= d;
    end
end

assign qn = ~q;

endmodule