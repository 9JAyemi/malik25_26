module twos_complement_assertions (
    input logic [3:0] a,
    input logic [3:0] twos_comp
);

    function automatic logic [3:0] model_twos_comp(input logic [3:0] val);
        logic [3:0] ones_comp_v;
        logic [3:0] inverted_v;
        begin
            ones_comp_v = ~val;
            inverted_v  = ones_comp_v + 4'b0001;
            model_twos_comp = inverted_v[3] ? (inverted_v + 4'b0001) : inverted_v;
        end
    endfunction

    // No RTL clock or reset; sample this combinational logic on the global formal clock.
    // Output matches the implemented combinational transform.
    check_output_matches_rtl: assert property (
        @($global_clock) twos_comp == model_twos_comp(a)
    );

    // Zero input produces zero output.
    check_zero_maps_to_zero: assert property (
        @($global_clock) (a == 4'h0) |-> (twos_comp == 4'h0)
    );

    // Input one also produces zero output.
    check_one_maps_to_zero: assert property (
        @($global_clock) (a == 4'h1) |-> (twos_comp == 4'h0)
    );

    // Inputs 1 through 8 take the extra increment path.
    check_extra_increment_region: assert property (
        @($global_clock) ((a >= 4'h1) && (a <= 4'h8)) |-> (twos_comp == ((~a) + 4'h2))
    );

    // Input zero and inputs 9 through 15 use the single increment path.
    check_single_increment_region: assert property (
        @($global_clock) ((a == 4'h0) || ((a >= 4'h9) && (a <= 4'hF))) |-> (twos_comp == ((~a) + 4'h1))
    );

    // Eight is the last input that takes the extra increment path.
    check_eight_boundary_value: assert property (
        @($global_clock) (a == 4'h8) |-> (twos_comp == 4'h9)
    );

    // Nine is the first input that skips the extra increment.
    check_nine_boundary_value: assert property (
        @($global_clock) (a == 4'h9) |-> (twos_comp == 4'h7)
    );

    // The maximum input maps to one.
    check_fifteen_maps_to_one: assert property (
        @($global_clock) (a == 4'hF) |-> (twos_comp == 4'h1)
    );

endmodule