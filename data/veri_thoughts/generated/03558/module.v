
module dff_asynchronous_set_reset(clk, rst, set, d, q, qn);

input clk, rst, set, d;
output q, qn;
reg q;

always @(posedge clk or negedge rst) begin
    if (~rst)
        q <= 1'b0;
    else if (~set)
        q <= 1'b1;
    else
        q <= d;
end

assign qn = ~q;

endmodule