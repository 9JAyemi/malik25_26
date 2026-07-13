
module d_flip_flop (
    input clk,
    input d,
    output reg q = 1'b0 );  // Initialize q to 0

    always @(posedge clk) begin
        q <= d; // Use blocking assignment inside always block
    end

endmodule
