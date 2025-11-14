module shift_reg_serial (
    input data_in,
    input shift,
    input clk,
    output reg q
);

reg [3:0] pipeline[2:0];

always @(posedge clk) begin
    pipeline[0] <= data_in;
    pipeline[1] <= pipeline[0];
    pipeline[2] <= pipeline[1];
    if (shift) begin
        pipeline[0] <= pipeline[1];
        pipeline[1] <= pipeline[2];
        pipeline[2] <= q;
    end
    q <= pipeline[2];
end

endmodule