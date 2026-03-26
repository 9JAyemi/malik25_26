module generate_HI_LO_sva (
    input logic clk,
    input logic HI,
    input logic LO,
    input logic pullup0_out,
    input logic pulldown0_out,
    input logic pwrgood_pp
);

    // HI matches pwrgood_pp AND pullup0_out.
    check_hi_definition: assert property (
        @(posedge clk) HI == (pwrgood_pp & pullup0_out)
    );

    // LO matches inverted pwrgood_pp AND inverted pulldown0_out.
    check_lo_definition: assert property (
        @(posedge clk) LO == ((~pwrgood_pp) & (~pulldown0_out))
    );

    // HI can only be high when pwrgood_pp is high.
    check_hi_requires_pwrgood: assert property (
        @(posedge clk) HI |-> pwrgood_pp
    );

    // HI can only be high when pullup0_out is high.
    check_hi_requires_pullup: assert property (
        @(posedge clk) HI |-> pullup0_out
    );

    // LO can only be high when pwrgood_pp is low.
    check_lo_requires_no_pwrgood: assert property (
        @(posedge clk) LO |-> ~pwrgood_pp
    );

    // LO can only be high when pulldown0_out is low.
    check_lo_requires_no_pulldown: assert property (
        @(posedge clk) LO |-> ~pulldown0_out
    );

    // pwrgood_pp low forces HI low.
    check_no_pwrgood_forces_hi_low: assert property (
        @(posedge clk) ~pwrgood_pp |-> ~HI
    );

    // pwrgood_pp high forces LO low.
    check_pwrgood_forces_lo_low: assert property (
        @(posedge clk) pwrgood_pp |-> ~LO
    );

    // pulldown0_out high forces LO low.
    check_pulldown_high_forces_lo_low: assert property (
        @(posedge clk) pulldown0_out |-> ~LO
    );

    // HI and LO cannot be high together.
    check_hi_lo_mutex: assert property (
        @(posedge clk) !(HI & LO)
    );

endmodule