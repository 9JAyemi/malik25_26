module mux_4to1_sva (
    input logic       clk,
    input logic       Y,
    input logic       D0,
    input logic       D1,
    input logic       D2,
    input logic       D3,
    input logic [1:0] SEL,
    input logic       EN
);

    // Combinational RTL; clk is an external sampling clock and there is no reset.

    // bufif0 drives Y to high impedance when EN is high.
    check_output_tristated_when_disabled: assert property (
        @(posedge clk) (EN === 1'b1) |-> (Y === 1'bz)
    );

    // When enabled, Y matches the implemented logic cone.
    check_enabled_output_matches_implemented_logic: assert property (
        @(posedge clk) (EN === 1'b0) |-> (Y === (D3 & SEL[0] & SEL[1]))
    );

    // With EN low and SEL[1] low, the final stage forces Y low.
    check_sel1_low_forces_zero_when_enabled: assert property (
        @(posedge clk) (EN === 1'b0 && SEL[1] === 1'b0) |-> (Y === 1'b0)
    );

    // With EN low and SEL equal 2'b10, Y remains low.
    check_sel_10_forces_zero_when_enabled: assert property (
        @(posedge clk) (EN === 1'b0 && SEL === 2'b10) |-> (Y === 1'b0)
    );

    // With EN low and SEL equal 2'b11, Y follows D3.
    check_sel_11_passes_d3_when_enabled: assert property (
        @(posedge clk) (EN === 1'b0 && SEL === 2'b11) |-> (Y === D3)
    );

endmodule