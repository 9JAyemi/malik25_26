
module Mealy_FSM_ROM(
    input clk,
    input reset,
    input x,
    output reg [2:0] count
    );
    
    reg [2:0] state, nextState;
    reg [5:0] ROM [0:11];
    
    parameter s0 = 0, s1 = 1, s2 = 2, s3 = 3, s4 = 4, s5 = 5;
    
    // set up ROM
    initial begin
        ROM[0]  <= 6'b000010; // s0, x = 0: 000010
        ROM[1]  <= 6'b001000; // s0, x = 1: 001000
        ROM[2]  <= 6'b001000; // s1, x = 0: 001000
        ROM[3]  <= 6'b010001; // s1, x = 0: 010001
        ROM[4]  <= 6'b010001; // s2, x = 0: 010001
        ROM[5]  <= 6'b011011; // s2, x = 0: 011011
        ROM[6]  <= 6'b011011; // s3, x = 0: 011011
        ROM[7]  <= 6'b100101; // s3, x = 0: 100101
        ROM[8]  <= 6'b100101; // s4, x = 0: 100101
        ROM[9]  <= 6'b101111; // s4, x = 0: 101111
        ROM[10] <= 6'b101111; // s5, x = 0: 101111
        ROM[11] <= 6'b000010; // s5, x = 0: 000010
    end
    
    // update state
    always @(posedge clk or posedge reset) begin
        if (reset) state <= s1;
        else state <= nextState;
    end
    
    
     
    
    
    always @(x or state) begin
        {nextState, count} <= ROM[(state * 2 + x + (!clk & !reset)) % 12];
    end           
endmodule