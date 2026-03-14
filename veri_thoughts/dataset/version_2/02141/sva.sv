module mux_sva (
    input logic CLK,
    input logic [3:0] D,
    input logic EN,
    input logic [1:0] SEL,
    input logic Y
);
    // When disabled, output must be 0.
    check_disabled_drives_zero: assert property (
        @(posedge CLK) (!EN) |-> (Y == 1'b0)
    );

    // When enabled and SEL==00, output selects D[0].
    check_enabled_sel00_maps: assert property (
        @(posedge CLK) (EN && (SEL == 2'b00)) |-> (Y == D[0])
    );

    // When enabled and SEL==01, output selects D[1].
    check_enabled_sel01_maps: assert property (
        @(posedge CLK) (EN && (SEL == 2'b01)) |-> (Y == D[1])
    );

    // When enabled and SEL==10, output selects D[2].
    check_enabled_sel10_maps: assert property (
        @(posedge CLK) (EN && (SEL == 2'b10)) |-> (Y == D[2])
    );

    // When enabled and SEL==11, output selects D[3].
    check_enabled_sel11_maps: assert property (
        @(posedge CLK) (EN && (SEL == 2'b11)) |-> (Y == D[3])
    );

    // On falling edge of EN, output must be 0 in the same cycle.
    check_en_fall_forces_zero: assert property (
        @(posedge CLK) $fell(EN) |-> (Y == 1'b0)
    );

    // While disabled and EN stable low, output stays 0 and stable.
    check_stable_zero_when_disabled: assert property (
        @(posedge CLK) (!EN && $stable(EN)) |-> ($stable(Y) && (Y == 1'b0))
    );

    // With EN high, SEL==00, and inputs stable, output is stable.
    check_stable_output_sel00: assert property (
        @(posedge CLK) (EN && $stable(EN) && (SEL == 2'b00) && $stable(SEL) && $stable(D[0])) |-> $stable(Y)
    );

    // With EN high, SEL==01, and inputs stable, output is stable.
    check_stable_output_sel01: assert property (
        @(posedge CLK) (EN && $stable(EN) && (SEL == 2'b01) && $stable(SEL) && $stable(D[1])) |-> $stable(Y)
    );

    // With EN high, SEL==10, and inputs stable, output is stable.
    check_stable_output_sel10: assert property (
        @(posedge CLK) (EN && $stable(EN) && (SEL == 2'b10) && $stable(SEL) && $stable(D[2])) |-> $stable(Y)
    );

    // With EN high, SEL==11, and inputs stable, output is stable.
    check_stable_output_sel11: assert property (
        @(posedge CLK) (EN && $stable(EN) && (SEL == 2'b11) && $stable(SEL) && $stable(D[3])) |-> $stable(Y)
    );
endmodule