module mux8to1_sva (
    input logic y,
    input logic s2,
    input logic s1,
    input logic s0,
    input logic d4,
    input logic d3,
    input logic d2,
    input logic d1,
    input logic d0
);

    // Select 000 routes d0 to y.
    check_select_000_routes_d0: assert property (
        @($global_clock) ({s2, s1, s0} === 3'b000) |-> (y === d0)
    );

    // Select 001 routes d1 to y.
    check_select_001_routes_d1: assert property (
        @($global_clock) ({s2, s1, s0} === 3'b001) |-> (y === d1)
    );

    // Select 010 routes d2 to y.
    check_select_010_routes_d2: assert property (
        @($global_clock) ({s2, s1, s0} === 3'b010) |-> (y === d2)
    );

    // Select 011 routes d3 to y.
    check_select_011_routes_d3: assert property (
        @($global_clock) ({s2, s1, s0} === 3'b011) |-> (y === d3)
    );

    // Select 100 routes d4 to y.
    check_select_100_routes_d4: assert property (
        @($global_clock) ({s2, s1, s0} === 3'b100) |-> (y === d4)
    );

    // Any unsupported or unknown select value drives y low.
    check_unimplemented_select_drives_zero: assert property (
        @($global_clock)
        !(
            ({s2, s1, s0} === 3'b000) ||
            ({s2, s1, s0} === 3'b001) ||
            ({s2, s1, s0} === 3'b010) ||
            ({s2, s1, s0} === 3'b011) ||
            ({s2, s1, s0} === 3'b100)
        ) |-> (y === 1'b0)
    );

    // Unselected inputs do not affect y when select and the chosen source are unchanged.
    check_unselected_inputs_do_not_affect_y: assert property (
        @($global_clock)
        $stable({s2, s1, s0}) &&
        (
            (({s2, s1, s0} === 3'b000) && $stable(d0)) ||
            (({s2, s1, s0} === 3'b001) && $stable(d1)) ||
            (({s2, s1, s0} === 3'b010) && $stable(d2)) ||
            (({s2, s1, s0} === 3'b011) && $stable(d3)) ||
            (({s2, s1, s0} === 3'b100) && $stable(d4)) ||
            !(
                ({s2, s1, s0} === 3'b000) ||
                ({s2, s1, s0} === 3'b001) ||
                ({s2, s1, s0} === 3'b010) ||
                ({s2, s1, s0} === 3'b011) ||
                ({s2, s1, s0} === 3'b100)
            )
        ) |-> $stable(y)
    );

endmodule