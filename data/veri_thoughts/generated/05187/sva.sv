module mux4to1_sva (
    input logic [3:0] in0,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] in3,
    input logic [1:0] sel,
    input logic [3:0] out
);

    // No RTL clock or reset; sample this combinational mux on the formal global clock.

    // When sel is 00, out matches in0.
    check_select_in0: assert property (
        @($global_clock) (sel === 2'b00) |-> (out === in0)
    );

    // When sel is 01, out matches in1.
    check_select_in1: assert property (
        @($global_clock) (sel === 2'b01) |-> (out === in1)
    );

    // When sel is 10, out matches in2.
    check_select_in2: assert property (
        @($global_clock) (sel === 2'b10) |-> (out === in2)
    );

    // When sel is 11, out matches in3.
    check_select_in3: assert property (
        @($global_clock) (sel === 2'b11) |-> (out === in3)
    );

endmodule