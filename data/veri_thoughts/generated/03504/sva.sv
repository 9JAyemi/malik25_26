module mux4to1_sva (
    input logic [3:0] in,
    input logic [1:0] sel,
    input logic out
);

    // No RTL clock or reset; sample this combinational mux on the formal global clock.
    // Pure combinational 4:1 mux: sel selects which in bit drives out.

    // sel 00 routes in[0] to out.
    check_sel_00_routes_in0: assert property (
        @($global_clock) (sel === 2'b00) |-> (out === in[0])
    );

    // sel 01 routes in[1] to out.
    check_sel_01_routes_in1: assert property (
        @($global_clock) (sel === 2'b01) |-> (out === in[1])
    );

    // sel 10 routes in[2] to out.
    check_sel_10_routes_in2: assert property (
        @($global_clock) (sel === 2'b10) |-> (out === in[2])
    );

    // All remaining select values take the default in[3] branch.
    check_default_routes_in3: assert property (
        @($global_clock) (sel !== 2'b00 && sel !== 2'b01 && sel !== 2'b10) |-> (out === in[3])
    );

endmodule