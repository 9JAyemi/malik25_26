module karnaugh_map_4bit_sva (
    input logic CLK,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic F
);
    // F=0 when ABCD=0000
    check_map_0000: assert property (
        @(posedge CLK) disable iff (1'b0) ({A,B,C,D} == 4'b0000) |-> (F == 1'b0)
    );
    // F=1 when ABCD=0001
    check_map_0001: assert property (
        @(posedge CLK) disable iff (1'b0) ({A,B,C,D} == 4'b0001) |-> (F == 1'b1)
    );
    // F=1 when ABCD=0010
    check_map_0010: assert property (
        @(posedge CLK) disable iff (1'b0) ({A,B,C,D} == 4'b0010) |-> (F == 1'b1)
    );
    // F=0 when ABCD=0011
    check_map_0011: assert property (
        @(posedge CLK) disable iff (1'b0) ({A,B,C,D} == 4'b0011) |-> (F == 1'b0)
    );
    // F=1 when ABCD=0100
    check_map_0100: assert property (
        @(posedge CLK) disable iff (1'b0) ({A,B,C,D} == 4'b0100) |-> (F == 1'b1)
    );
    // F=0 when ABCD=0101
    check_map_0101: assert property (
        @(posedge CLK) disable iff (1'b0) ({A,B,C,D} == 4'b0101) |-> (F == 1'b0)
    );
    // F=0 when ABCD=0110
    check_map_0110: assert property (
        @(posedge CLK) disable iff (1'b0) ({A,B,C,D} == 4'b0110) |-> (F == 1'b0)
    );
    // F=1 when ABCD=0111
    check_map_0111: assert property (
        @(posedge CLK) disable iff (1'b0) ({A,B,C,D} == 4'b0111) |-> (F == 1'b1)
    );
    // F=0 when ABCD=1000
    check_map_1000: assert property (
        @(posedge CLK) disable iff (1'b0) ({A,B,C,D} == 4'b1000) |-> (F == 1'b0)
    );
    // F=1 when ABCD=1001
    check_map_1001: assert property (
        @(posedge CLK) disable iff (1'b0) ({A,B,C,D} == 4'b1001) |-> (F == 1'b1)
    );
    // F=1 when ABCD=1010
    check_map_1010: assert property (
        @(posedge CLK) disable iff (1'b0) ({A,B,C,D} == 4'b1010) |-> (F == 1'b1)
    );
    // F=0 when ABCD=1011
    check_map_1011: assert property (
        @(posedge CLK) disable iff (1'b0) ({A,B,C,D} == 4'b1011) |-> (F == 1'b0)
    );
    // F=0 when ABCD=1100
    check_map_1100: assert property (
        @(posedge CLK) disable iff (1'b0) ({A,B,C,D} == 4'b1100) |-> (F == 1'b0)
    );
    // F=1 when ABCD=1101
    check_map_1101: assert property (
        @(posedge CLK) disable iff (1'b0) ({A,B,C,D} == 4'b1101) |-> (F == 1'b1)
    );
    // F=1 when ABCD=1110
    check_map_1110: assert property (
        @(posedge CLK) disable iff (1'b0) ({A,B,C,D} == 4'b1110) |-> (F == 1'b1)
    );
    // F=0 when ABCD=1111
    check_map_1111: assert property (
        @(posedge CLK) disable iff (1'b0) ({A,B,C,D} == 4'b1111) |-> (F == 1'b0)
    );
endmodule