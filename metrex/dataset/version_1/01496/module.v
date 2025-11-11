module top_module (
    input clk,
    input reset,
    input enable1, // Enable input for counter 1
    input enable2, // Enable input for counter 2
    output [3:0] q1, // 4-bit output from counter 1
    output [3:0] q2, // 4-bit output from counter 2
    output [3:0] final_output // Result of bitwise OR operation
);

    // Define two 4-bit binary counters with asynchronous reset and enable inputs
    reg [3:0] counter1;
    reg [3:0] counter2;
    
    always @(posedge clk or posedge reset) begin
        if (reset) begin
            counter1 <= 4'b0;
            counter2 <= 4'b0;
        end else if (enable1) begin
            counter1 <= counter1 + 1;
        end else if (enable2) begin
            counter2 <= counter2 + 1;
        end
    end
    
    assign q1 = counter1;
    assign q2 = counter2;
    
    // Define a functional module that takes in both of the 4-bit outputs from the counters
    // and outputs the bitwise OR of the two outputs
    assign final_output = q1 | q2;

endmodule