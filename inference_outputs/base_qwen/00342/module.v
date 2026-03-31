
module shift_register (
    input clk,
    input shift_dir,
    input parallel_load,
    input [7:0] data_in,
    output [7:0] serial_out,
    output [7:0] parallel_out
);

    reg [7:0] shift_reg;

    always @(posedge clk) begin
        if (parallel_load) begin
            shift_reg <= data_in;
        end else begin
            if (shift_dir) begin
                shift_reg <= {shift_reg[6:0], 1'b0};
            end else begin
                shift_reg <= {1'b0, shift_reg[7:1]};
            end
        end
    end

    assign serial_out = shift_reg[0];
    assign parallel_out = shift_reg;

endmodule
