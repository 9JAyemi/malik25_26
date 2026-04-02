module two_bit_comparator_sva (
    input logic [1:0] A,
    input logic [1:0] B,
    input logic [1:0] C
);
    // C should be 00 when A equals B
    compare_equal: assert property (
        @(posedge CLK) disable iff (!RESETn) (A == B) |-> (C == 2'b00)
    );
    // C should be 01 when A is greater than B
    compare_greater: assert property (
        @(posedge CLK) disable iff (!RESETn) (A > B) |-> (C == 2'b01)
    );
    // C should be 10 when A is less than B
    compare_less: assert property (
        @(posedge CLK) disable iff (!RESETn) (A < B) |-> (C == 2'b10)
    );
endmodule