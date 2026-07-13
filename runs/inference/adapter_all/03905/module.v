module shift_register (
    input clk,
    input [7:0] data,
    output reg [7:0] shifted_data
);

always @(posedge clk) begin
    shifted_data <= {shifted_data[6:0], data[7]};
end

endmodule