
module shift_comp (
    input clk,
    input reset,
    input [15:0] serial_in,
    input shift_direction,
    output [15:0] serial_out,
    output final_output
);

    // Define the 16-bit shift register module
    reg [15:0] shift_reg;
    always @(posedge clk) begin
        if (reset) begin
            shift_reg <= 16'b0;
        end else begin
            if (shift_direction) begin
                shift_reg <= {shift_reg[14:0], serial_in[0]};
            end else begin
                shift_reg <= {serial_in[15], shift_reg[15:1]};
            end
        end
    end
    assign serial_out = shift_reg;

    // Define the 4-bit magnitude comparator module
    reg [3:0] constant = 4'b1010;
    wire equal, greater;

    comparator comparator0 (
        .a(shift_reg[3:0]),
        .b(constant),
        .equal(equal),
        .greater(greater)
    );

    assign final_output = equal | greater;

endmodule

module comparator (
    input [3:0] a,
    input [3:0] b,
    output equal,
    output greater
);
    assign equal = (a == b);
    assign greater = (a > b);
endmodule
