module BLOCK1_sva (
    input logic PIN1,
    input logic PIN2,
    input logic GIN1,
    input logic GIN2,
    input logic PHI,
    input logic POUT,
    input logic GOUT
);

    // POUT must implement the NOR of PIN1 and PIN2.
    check_pout_equation: assert property (
        @(posedge PHI) POUT == ~(PIN1 | PIN2)
    );

    // GOUT must implement the inverted AND of GIN2 with (PIN2 | GIN1).
    check_gout_equation: assert property (
        @(posedge PHI) GOUT == ~(GIN2 & (PIN2 | GIN1))
    );

    // If either PIN input is high, POUT must be low.
    check_pout_low_when_any_pin_high: assert property (
        @(posedge PHI) ((PIN1 == 1'b1) || (PIN2 == 1'b1)) |-> (POUT == 1'b0)
    );

    // If both PIN inputs are low, POUT must be high.
    check_pout_high_when_both_pins_low: assert property (
        @(posedge PHI) ((PIN1 == 1'b0) && (PIN2 == 1'b0)) |-> (POUT == 1'b1)
    );

    // If GIN2 is low, GOUT must be high.
    check_gout_high_when_gin2_low: assert property (
        @(posedge PHI) (GIN2 == 1'b0) |-> (GOUT == 1'b1)
    );

    // If both PIN2 and GIN1 are low, GOUT must be high.
    check_gout_high_when_or_term_low: assert property (
        @(posedge PHI) ((PIN2 == 1'b0) && (GIN1 == 1'b0)) |-> (GOUT == 1'b1)
    );

    // If GIN2 and PIN2 are high, GOUT must be low.
    check_gout_low_when_gin2_and_pin2_high: assert property (
        @(posedge PHI) ((GIN2 == 1'b1) && (PIN2 == 1'b1)) |-> (GOUT == 1'b0)
    );

    // If GIN2 and GIN1 are high, GOUT must be low.
    check_gout_low_when_gin2_and_gin1_high: assert property (
        @(posedge PHI) ((GIN2 == 1'b1) && (GIN1 == 1'b1)) |-> (GOUT == 1'b0)
    );

endmodule