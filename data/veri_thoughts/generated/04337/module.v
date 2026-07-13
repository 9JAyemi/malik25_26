
module shift_register (
    input clk,
    input parallel_load,
    input serial_in,
    output serial_out,
    input [3:0] data_in
);

reg [3:0] pipeline [0:2];

always @(posedge clk) begin
    if (parallel_load) begin
        pipeline[0] <= data_in;
    end else begin
        pipeline[0] <= pipeline[1];
    end
    pipeline[1] <= pipeline[2];
    pipeline[2] <= serial_in;
end

assign serial_out = pipeline[2];

endmodule