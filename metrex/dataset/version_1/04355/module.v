module top_module (
    input clk,
    input areset,  // async active-high reset to zero
    input load,
    input ena,
    input [3:0] data,
    input d,
    output [6:0] q
);

    // 4-bit shift register with asynchronous reset, synchronous load, and enable
    reg [3:0] shift_reg;
    always @(posedge clk or posedge areset) begin
        if (areset) begin
            shift_reg <= 4'b0;
        end else if (load & ena) begin
            shift_reg <= data;
        end else if (ena) begin
            shift_reg <= {shift_reg[2:0], d};
        end
    end
    
    // 3-bit shift register using a single D flip-flop
    reg [2:0] shift_reg_3;
    always @(posedge clk) begin
        shift_reg_3 <= {shift_reg_3[1:0], d};
    end
    
    // Functional module that outputs the bitwise OR of the values of both shift registers
    assign q = {shift_reg, shift_reg_3} | 3'b0;
    
endmodule