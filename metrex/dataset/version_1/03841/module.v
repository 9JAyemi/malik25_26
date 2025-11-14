
module shift_reg (
    input [3:0] data_in,
    input load,
    input clk,
    output reg [3:0] q
);

always @(posedge clk) begin
    if(load) begin
        q[3] <= data_in;
        q[2] <= q[3];
        q[1] <= q[2];
        q[0] <= q[1];
    end
    else begin
        q[3] <= q[2];
        q[2] <= q[1];
        q[1] <= q[0];
        q[0] <= data_in;
    end
end

endmodule