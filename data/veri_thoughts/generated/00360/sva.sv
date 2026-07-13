module BLOCK1A_sva (
    input logic PIN2,
    input logic GIN1,
    input logic GIN2,
    input logic PHI,
    input logic GOUT
);

    // GOUT registers the implemented Boolean function on each rising PHI edge.
    check_gout_update_function: assert property (
        @(posedge PHI)
        1'b1 |=> (GOUT == ~($past(GIN2) & ($past(PIN2) | $past(GIN1))))
    );

    // If GIN2 is low at a clock edge, the next registered GOUT is high.
    check_gin2_low_forces_gout_high: assert property (
        @(posedge PHI)
        (!GIN2) |=> (GOUT == 1'b1)
    );

    // If GIN2 and PIN2 are high at a clock edge, the next registered GOUT is low.
    check_gin2_and_pin2_force_gout_low: assert property (
        @(posedge PHI)
        (GIN2 && PIN2) |=> (GOUT == 1'b0)
    );

    // If GIN2 and GIN1 are high at a clock edge, the next registered GOUT is low.
    check_gin2_and_gin1_force_gout_low: assert property (
        @(posedge PHI)
        (GIN2 && GIN1) |=> (GOUT == 1'b0)
    );

    // If only GIN2 is high at a clock edge, the next registered GOUT is high.
    check_only_gin2_high_sets_gout_high: assert property (
        @(posedge PHI)
        (GIN2 && !PIN2 && !GIN1) |=> (GOUT == 1'b1)
    );

endmodule