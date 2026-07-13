module mux_4to1_enable_sva (
    input logic [7:0] D0,
    input logic [7:0] D1,
    input logic [7:0] D2,
    input logic [7:0] D3,
    input logic [1:0] SEL,
    input logic EN,
    input logic [7:0] Y
);

    // When disabled, Y must be zero.
    check_disabled_forces_zero: assert property (
        @($global_clock) (!EN) |-> (Y == 8'h00)
    );

    // When enabled and SEL is 00, Y must equal D0.
    check_select_00_routes_d0: assert property (
        @($global_clock) (EN && (SEL == 2'b00)) |-> (Y == D0)
    );

    // When enabled and SEL is 01, Y must equal D1.
    check_select_01_routes_d1: assert property (
        @($global_clock) (EN && (SEL == 2'b01)) |-> (Y == D1)
    );

    // When enabled and SEL is 10, Y must equal D2.
    check_select_10_routes_d2: assert property (
        @($global_clock) (EN && (SEL == 2'b10)) |-> (Y == D2)
    );

    // When enabled and SEL is 11, Y must equal D3.
    check_select_11_routes_d3: assert property (
        @($global_clock) (EN && (SEL == 2'b11)) |-> (Y == D3)
    );

endmodule