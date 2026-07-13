module Span12Mux_s5_v_assertions (
    input logic CLK,
    input logic [11:0] I,
    input logic O
);
    // The output O is 1'b1 when I is 12'b000000000001
    output_1: assert property (
        @(posedge CLK) $rose(I == 12'b000000000001) |-> O == 1'b1
    );
    // The output O is 1'b0 when I is 12'b000000000010
    output_2: assert property (
        @(posedge CLK) $rose(I == 12'b000000000010) |-> O == 1'b0
    );
    // The output O is 1'b1 when I is 12'b000000000100
    output_3: assert property (
        @(posedge CLK) $rose(I == 12'b000000000100) |-> O == 1'b1
    );
    // The output O is 1'b0 when I is 12'b000000001000
    output_4: assert property (
        @(posedge CLK) $rose(I == 12'b000000001000) |-> O == 1'b0
    );
    // The output O is 1'b1 when I is 12'b000000010000
    output_5: assert property (
        @(posedge CLK) $rose(I == 12'b000000010000) |-> O == 1'b1
    );
    // The output O is 1'b0 when I is 12'b000000100000
    output_6: assert property (
        @(posedge CLK) $rose(I == 12'b000000100000) |-> O == 1'b0
    );
    // The output O is 1'b1 when I is 12'b000001000000
    output_7: assert property (
        @(posedge CLK) $rose(I == 12'b000001000000) |-> O == 1'b1
    );
    // The output O is 1'b0 when I is 12'b000010000000
    output_8: assert property (
        @(posedge CLK) $rose(I == 12'b000010000000) |-> O == 1'b0
    );
    // The output O is 1'b1 when I is 12'b000100000000
    output_9: assert property (
        @(posedge CLK) $rose(I == 12'b000100000000) |-> O == 1'b1
    );
    // The output O is 1'b0 when I is 12'b001000000000
    output_10: assert property (
        @(posedge CLK) $rose(I == 12'b001000000000) |-> O == 1'b0
    );
    // The output O is 1'b1 when I is 12'b010000000000
    output_11: assert property (
        @(posedge CLK) $rose(I == 12'b010000000000) |-> O == 1'b1
    );
    // The output O is 1'b0 when I is 12'b100000000000
    output_12: assert property (
        @(posedge CLK) $rose(I == 12'b100000000000) |-> O == 1'b0
    );
    // The output O is 1'b0 when I is not one of the specified values
    output_13: assert property (
        @(posedge CLK) $rose(I != 12'b000000000001) && $rose(I != 12'b000000000010) && $rose(I != 12'b000000000100) && $rose(I != 12'b000000001000) && $rose(I != 12'b000000010000) && $rose(I != 12'b000000100000) && $rose(I != 12'b000001000000) && $rose(I != 12'b000010000000) && $rose(I != 12'b000100000000) && $rose(I != 12'b001000000000) && $rose(I != 12'b010000000000) && $rose(I != 12'b100000000000) |-> O == 1'b0
    );
endmodule