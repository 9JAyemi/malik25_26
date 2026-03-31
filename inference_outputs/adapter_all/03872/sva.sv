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

    // When enabled and SEL==00, Y must equal D0.
    check_sel_00_routes_d0: assert property (
        @($global_clock) (EN && (SEL == 2'b00)) |-> (Y == D0)
    );

    // When enabled and SEL==01, Y must equal D1.
    check_sel_01_routes_d1: assert property (
        @($global_clock) (EN && (SEL == 2'b01)) |-> (Y == D1)
    );

    // When enabled and SEL==10, Y must equal D2.
    check_sel_10_routes_d2: assert property (
        @($global_clock) (EN && (SEL == 2'b10)) |-> (Y == D2)
    );

    // When enabled and SEL==11, Y must equal D3.
    check_sel_11_routes_d3: assert property (
        @($global_clock) (EN && (SEL == 2'b11)) |-> (Y == D3)
    );

    // With EN and SEL held stable, a stable data input must keep Y stable.
    check_data_stability_when_selected: assert property (
        @($global_clock)
        (EN && $stable(EN) && $stable(SEL) &&
         ((SEL == 2'b00 && $stable(D0)) ||
          (SEL == 2'b01 && $stable(D1)) ||
          (SEL == 2'b10 && $stable(D2)) ||
          (SEL == 2'b11 && $stable(D3))))
        |-> $stable(Y)
    );

    // With EN and SEL held stable, a stable Y must come from a stable data input.
    check_output_stability_implies_selected_input_stability: assert property (
        @($global_clock)
        (EN && $stable(EN) && $stable(SEL) && $stable(Y) &&
         ((SEL == 2'b00 && (Y == D0)) ||
          (SEL == 2'b01 && (Y == D1)) ||
          (SEL == 2'b10 && (Y == D2)) ||
          (SEL == 2'b11 && (Y == D3))))
        |-> (
            ((SEL == 2'b00 && $stable(D0)) ||
             (SEL == 2'b01 && $stable(D1)) ||
             (SEL == 2'b10 && $stable(D2)) ||
             (SEL == 2'b11 && $stable(D3)))
        )
    );

endmodule