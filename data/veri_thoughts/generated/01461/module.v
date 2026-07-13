
module top_module (
    input clk,
    input reset,       // Asynchronous reset
    input slowena,     // Enable input for decade counter
    input [2:0] select,// Select input to choose between 3-to-4 wire connection and decade counter
    input [3:0] a,b,c,       // Inputs for 3-to-4 wire connection
    output [3:0] q     // Final 4-bit output from functional module
);

    // 3-to-4 wire connection module
    wire [3:0] w;
    assign w = (select == 3'b000) ? a : (select == 3'b001) ? b : (select == 3'b010) ? c : 4'b0000;

    // Decade counter module
    reg [3:0] counter;
    always @(posedge clk or negedge reset) begin
        if (!reset) begin
            counter <= 0;
        end else if (slowena) begin
            counter <= counter + 1;
        end
    end

    // Functional module
    assign q = (select == 3'b011) ? counter : w;

endmodule
