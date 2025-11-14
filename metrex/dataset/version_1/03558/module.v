
module shift_reg (
    input clk,
    input rst,
    input serial_in,
    input parallel_in,
    output serial_out
);

parameter WIDTH = 4;

reg [WIDTH-1:0] reg_data;

always @(posedge clk) begin
    if (rst) begin
        reg_data <= {WIDTH{1'b0}};
    end else begin
        if (parallel_in) begin
            reg_data <= {serial_in, reg_data[WIDTH-2:0]};
        end else begin
            reg_data <= {reg_data[WIDTH-2:0], serial_in};
        end
    end
end

assign serial_out = reg_data[WIDTH-1];

endmodule