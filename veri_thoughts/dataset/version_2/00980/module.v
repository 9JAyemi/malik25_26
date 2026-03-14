
module shift_reg (
    input clk,
    input reset,
    input load,
    input shift_left,
    input shift_right,
    input [15:0] data_in,
    output [15:0] data_out
);

    parameter WIDTH = 16; // configurable width of shift register
    reg [WIDTH-1:0] shift_reg; // register width matches the parameter

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            shift_reg <= 0;
        end else if (load) begin
            shift_reg <= data_in; // range selection not needed for full-width load
        end else if (shift_left) begin
            shift_reg <= {shift_reg[14:0], 1'b0}; // shift left operation
        end else if (shift_right) begin
            shift_reg <= {1'b0, shift_reg[15:1]}; // shift right operation
        end
    end

    assign data_out = shift_reg; // no padding needed for full-width output

endmodule