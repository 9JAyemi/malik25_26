module and_en_sva(
    input logic [2:0] a,
    input logic [2:0] b,
    input logic [2:0] c,
    input logic en,
    input logic y
);

    // y must match the RTL ternary expression.
    check_output_matches_function: assert property (
        @($global_clock) (y == (en ? &(a & b & c) : 1'b0))
    );

    // en low forces y low.
    check_disabled_forces_low: assert property (
        @($global_clock) (!en) |-> (y == 1'b0)
    );

    // en high makes y equal the reduced AND of a, b, and c.
    check_enabled_matches_and: assert property (
        @($global_clock) en |-> (y == &(a & b & c))
    );

    // A high y requires enable to be high.
    check_high_output_requires_enable: assert property (
        @($global_clock) y |-> en
    );

    // A high y requires every combined AND bit to be high.
    check_high_output_requires_all_and_bits: assert property (
        @($global_clock) y |-> (&(a & b & c))
    );

    // With enable and all combined AND bits high, y must be high.
    check_all_high_inputs_drive_high: assert property (
        @($global_clock) (en && &(a & b & c)) |-> (y == 1'b1)
    );

    // With enable and any combined AND bit low, y must be low.
    check_any_low_input_forces_low: assert property (
        @($global_clock) (en && !(&(a & b & c))) |-> (y == 1'b0)
    );

endmodule