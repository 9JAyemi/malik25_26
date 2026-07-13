module mux4to1_sva (
    input logic [3:0] in0,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] in3,
    input logic [1:0] sel,
    input logic out
);

    // sel=00 drives out with the LSB of in0.
    check_select_in0: assert property (
        @($global_clock) (sel === 2'b00) |-> (out === in0[0])
    );

    // sel=01 drives out with the LSB of in1.
    check_select_in1: assert property (
        @($global_clock) (sel === 2'b01) |-> (out === in1[0])
    );

    // sel=10 drives out with the LSB of in2.
    check_select_in2: assert property (
        @($global_clock) (sel === 2'b10) |-> (out === in2[0])
    );

    // sel=11 drives out with the LSB of in3.
    check_select_in3: assert property (
        @($global_clock) (sel === 2'b11) |-> (out === in3[0])
    );

endmodule