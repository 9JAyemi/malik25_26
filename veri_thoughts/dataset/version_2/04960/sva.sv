module mux6_sva #(parameter WIREWIDTH = 1) (
    input logic [2:0] s,
    input logic [WIREWIDTH-1:0] d0,
    input logic [WIREWIDTH-1:0] d1,
    input logic [WIREWIDTH-1:0] d2,
    input logic [WIREWIDTH-1:0] d3,
    input logic [WIREWIDTH-1:0] d4,
    input logic [WIREWIDTH-1:0] d5,
    input logic [WIREWIDTH-1:0] o
);

    // Select 000 routes d0 to the output.
    check_select_000_routes_d0: assert property (
        @($global_clock) (s === 3'b000) |-> (o === d0)
    );

    // Select 001 routes d1 to the output.
    check_select_001_routes_d1: assert property (
        @($global_clock) (s === 3'b001) |-> (o === d1)
    );

    // Select 010 routes d2 to the output.
    check_select_010_routes_d2: assert property (
        @($global_clock) (s === 3'b010) |-> (o === d2)
    );

    // Select 011 routes d3 to the output.
    check_select_011_routes_d3: assert property (
        @($global_clock) (s === 3'b011) |-> (o === d3)
    );

    // Select 100 routes d4 to the output.
    check_select_100_routes_d4: assert property (
        @($global_clock) (s === 3'b100) |-> (o === d4)
    );

    // All other select values route d5 to the output.
    check_default_routes_d5: assert property (
        @($global_clock)
        !((s === 3'b000) || (s === 3'b001) || (s === 3'b010) || (s === 3'b011) || (s === 3'b100))
        |-> (o === d5)
    );

endmodule