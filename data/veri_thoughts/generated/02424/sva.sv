module comparator_sva (
    // DUT ports
    input logic [2:0] A,
    input logic [2:0] B,
    input logic [1:0] result,
    // Formal clock (DUT has no clock/reset; pure combinational)
    input logic clk
);

    // Result never encodes 2'b11.
    check_result_no_11: assert property (
        @(posedge clk) (result != 2'b11)
    );

    // If A > B then result is 2'b10.
    map_AgtB_to_10: assert property (
        @(posedge clk) (A > B) |-> (result == 2'b10)
    );

    // If result is 2'b10 then A > B.
    map_10_to_AgtB: assert property (
        @(posedge clk) (result == 2'b10) |-> (A > B)
    );

    // If B > A then result is 2'b01.
    map_BgtA_to_01: assert property (
        @(posedge clk) (B > A) |-> (result == 2'b01)
    );

    // If result is 2'b01 then B > A.
    map_01_to_BgtA: assert property (
        @(posedge clk) (result == 2'b01) |-> (B > A)
    );

    // If A == B then result is 2'b00.
    map_AeqB_to_00: assert property (
        @(posedge clk) (A == B) |-> (result == 2'b00)
    );

    // If result is 2'b00 then A == B.
    map_00_to_AeqB: assert property (
        @(posedge clk) (result == 2'b00) |-> (A == B)
    );

endmodule