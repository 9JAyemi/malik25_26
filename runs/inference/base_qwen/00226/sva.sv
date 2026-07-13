module desxor1_assertions(
    input logic CLK,
    input logic RESETn,
    input logic [47:0] e,
    input logic [47:0] k,
    output logic [5:0] b1x,
    output logic [5:0] b2x,
    output logic [5:0] b3x,
    output logic [5:0] b4x,
    output logic [5:0] b5x,
    output logic [5:0] b6x,
    output logic [5:0] b7x,
    output logic [5:0] b8x
);
    // Sequential logic is not present, so all assertions are clocked.
    
    // XX is calculated as k XOR e
    xor_calculation: assert property (
        @(posedge CLK) disable iff (!RESETn) XX == (k ^ e)
    );
    
    // b1x is the lower 6 bits of XX
    b1x_assignment: assert property (
        @(posedge CLK) disable iff (!RESETn) b1x == XX[5:0]
    );
    
    // b2x is bits 11 to 6 of XX
    b2x_assignment: assert property (
        @(posedge CLK) disable iff (!RESETn) b2x == XX[11:6]
    );
    
    // b3x is bits 17 to 12 of XX
    b3x_assignment: assert property (
        @(posedge CLK) disable iff (!RESETn) b3x == XX[17:12]
    );
    
    // b4x is bits 23 to 18 of XX
    b4x_assignment: assert property (
        @(posedge CLK) disable iff (!RESETn) b4x == XX[23:18]
    );
    
    // b5x is bits 29 to 24 of XX
    b5x_assignment: assert property (
        @(posedge CLK) disable iff (!RESETn) b5x == XX[29:24]
    );
    
    // b6x is bits 35 to 30 of XX
    b6x_assignment: assert property (
        @(posedge CLK) disable iff (!RESETn) b6x == XX[35:30]
    );
    
    // b7x is bits 41 to 36 of XX
    b7x_assignment: assert property (
        @(posedge CLK) disable iff (!RESETn) b7x == XX[41:36]
    );
    
    // b8x is the upper 6 bits of XX
    b8x_assignment: assert property (
        @(posedge CLK) disable iff (!RESETn) b8x == XX[47:42]
    );
endmodule