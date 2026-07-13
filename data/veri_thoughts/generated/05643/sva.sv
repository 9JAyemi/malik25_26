module mux4to1_sva (
    input logic       clk,
    input logic [1:0] S,
    input logic       D0,
    input logic       D1,
    input logic       D2,
    input logic       D3,
    input logic       OE,
    input logic       Y
);

    // Y always matches the RTL mux expression.
    check_output_matches_rtl: assert property (
        @(posedge clk) disable iff (1'b0)
        Y == ((S == 2'b00) ? (OE ? D0 : 1'b0) :
              (S == 2'b01) ? (OE ? D1 : 1'b0) :
              (S == 2'b10) ? (OE ? D2 : 1'b0) :
              (S == 2'b11) ? (OE ? D3 : 1'b0) : 1'b0)
    );

    // Disabling the output forces Y low.
    check_oe_low_forces_zero: assert property (
        @(posedge clk) disable iff (1'b0)
        (!OE) |-> (Y == 1'b0)
    );

    // With output enabled and S=00, Y selects D0.
    check_select_d0_when_enabled: assert property (
        @(posedge clk) disable iff (1'b0)
        (OE && (S == 2'b00)) |-> (Y == D0)
    );

    // With output enabled and S=01, Y selects D1.
    check_select_d1_when_enabled: assert property (
        @(posedge clk) disable iff (1'b0)
        (OE && (S == 2'b01)) |-> (Y == D1)
    );

    // With output enabled and S=10, Y selects D2.
    check_select_d2_when_enabled: assert property (
        @(posedge clk) disable iff (1'b0)
        (OE && (S == 2'b10)) |-> (Y == D2)
    );

    // With output enabled and S=11, Y selects D3.
    check_select_d3_when_enabled: assert property (
        @(posedge clk) disable iff (1'b0)
        (OE && (S == 2'b11)) |-> (Y == D3)
    );

endmodule