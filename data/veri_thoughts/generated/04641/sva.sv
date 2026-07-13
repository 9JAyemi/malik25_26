module RAT_Mux4x1_8_0_1_sva (
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [7:0] C,
    input logic [7:0] D,
    input logic [1:0] SEL,
    input logic [7:0] X
);

    // X must match A when SEL selects input 0.
    check_sel_00_routes_a: assert property (
        @($global_clock) (SEL === 2'b00) |-> (X === A)
    );

    // X must match B when SEL selects input 1.
    check_sel_01_routes_b: assert property (
        @($global_clock) (SEL === 2'b01) |-> (X === B)
    );

    // X must match C when SEL selects input 2.
    check_sel_10_routes_c: assert property (
        @($global_clock) (SEL === 2'b10) |-> (X === C)
    );

    // X must match D when SEL selects input 3.
    check_sel_11_routes_d: assert property (
        @($global_clock) (SEL === 2'b11) |-> (X === D)
    );

endmodule