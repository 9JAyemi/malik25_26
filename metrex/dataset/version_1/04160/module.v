
module shift_register (
    input clk,
    input load,
    input shift_enable,
    input [3:0] data_in,
    output reg [3:0] data_out
);

reg [3:0] shift_reg;

always @(posedge clk) begin
    if (load) begin
        shift_reg <= data_in;
    end else if (shift_enable) begin
        shift_reg <= {shift_reg[2:0], 1'b0};
    end
    data_out <= shift_reg;
end

endmodule