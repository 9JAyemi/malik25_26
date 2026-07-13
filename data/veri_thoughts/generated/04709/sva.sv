module xor_and_sva (
    input logic c_in,
    input logic d_in,
    input logic out1
);

    // Combinational DUT with no reset; sample behavior on input edges.

    // On c_in rising, out1 must match the RTL equation.
    check_out1_func_on_c_rise: assert property (
        @(posedge c_in) out1 == ((c_in & d_in) ^ d_in)
    );

    // On c_in falling, out1 must match the RTL equation.
    check_out1_func_on_c_fall: assert property (
        @(negedge c_in) out1 == ((c_in & d_in) ^ d_in)
    );

    // On d_in rising, out1 must match the RTL equation.
    check_out1_func_on_d_rise: assert property (
        @(posedge d_in) out1 == ((c_in & d_in) ^ d_in)
    );

    // On d_in falling, out1 must match the RTL equation.
    check_out1_func_on_d_fall: assert property (
        @(negedge d_in) out1 == ((c_in & d_in) ^ d_in)
    );

    // On any input transition, c_in high forces out1 low.
    check_c_high_forces_out1_low: assert property (
        @(posedge c_in or negedge c_in or posedge d_in or negedge d_in)
        (c_in == 1'b1) |-> (out1 == 1'b0)
    );

    // On any input transition, d_in low forces out1 low.
    check_d_low_forces_out1_low: assert property (
        @(posedge c_in or negedge c_in or posedge d_in or negedge d_in)
        (d_in == 1'b0) |-> (out1 == 1'b0)
    );

    // On any input transition, c_in low makes out1 follow d_in.
    check_c_low_makes_out1_follow_d: assert property (
        @(posedge c_in or negedge c_in or posedge d_in or negedge d_in)
        (c_in == 1'b0) |-> (out1 == d_in)
    );

endmodule