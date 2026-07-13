
module min_shift_reg(
    input clk, 
    input areset,  // Async active-high reset to zero
    input load,
    input ena,
    input [7:0] a, b, c, d,    // Four 8-bit unsigned numbers as input
    output [3:0] q);           // 4-bit output from the shift register
    
    // Priority Encoder module to find the minimum of four inputs
    priority_encoder pe(
        .in({a, b, c, d}),
        .out(min_val)
    );
    
    // 4-bit shift register with asynchronous reset, synchronous load and enable
    reg [3:0] shift_reg;
    
    always @(posedge clk or posedge areset) begin
        if (areset) begin
            shift_reg <= 0;
        end else if (load) begin
            shift_reg <= min_val;
        end else if (ena) begin
            shift_reg <= {shift_reg[2:0], 1'b0};
        end
    end
    
    // Functional module to feed priority encoder output to shift register
    wire [1:0] min_val;
    
    assign q = shift_reg;
    
endmodule
module priority_encoder(
    input [31:0] in,
    output reg [1:0] out
);

    always @* begin
        if (in[7:0] < in[15:8]) begin
            out = 2'b00;
        end else if (in[15:8] < in[23:16]) begin
            out = 2'b01;
        end else if (in[23:16] < in[31:24]) begin
            out = 2'b10;
        end else begin
            out = 2'b11;
        end
    end
    
endmodule