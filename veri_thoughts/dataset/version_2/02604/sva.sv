module carry_select_adder_sva (
    input logic CLK,
    input logic [99:0] a,
    input logic [99:0] b,
    input logic cin,
    input logic cout,
    input logic [99:0] sum
);
    // sum is a mux of a and b selected by cout.
    check_sum_mux: assert property (
        @(posedge CLK) sum == (cout ? b : a)
    );

    // cout equals the carry-out of adding a[8:0], b[8:0], and cin.
    check_cout_is_low9_carry: assert property (
        @(posedge CLK) cout == ((a[8:0] + b[8:0] + cin) >= 10'd512)
    );

    // cout cannot change if a[8:0], b[8:0], and cin are stable.
    check_cout_stable_when_low9_and_cin_stable: assert property (
        @(posedge CLK) ($stable(a[8:0]) && $stable(b[8:0]) && $stable(cin)) |-> $stable(cout)
    );

    // If low 9 bits of a and b are zero and cin is zero, cout must be zero.
    check_cout_zero_when_no_generate_no_cin: assert property (
        @(posedge CLK) ((a[8:0] == 9'd0) && (b[8:0] == 9'd0) && (cin == 1'b0)) |-> (cout == 1'b0)
    );

    // If low 9 bits of a and b are all ones, cout must be one.
    check_cout_one_when_low9_all_ones: assert property (
        @(posedge CLK) ((a[8:0] == 9'h1FF) && (b[8:0] == 9'h1FF)) |-> (cout == 1'b1)
    );

    // If all low 9 bits propagate (a^b == all 1s) and cin is one, cout must be one.
    check_cout_one_when_all_propagate_and_cin1: assert property (
        @(posedge CLK) (((a[8:0] ^ b[8:0]) == 9'h1FF) && (cin == 1'b1)) |-> (cout == 1'b1)
    );

    // sum remains stable when a, b, and cout are stable.
    check_sum_stable_when_inputs_stable: assert property (
        @(posedge CLK) ($stable(a) && $stable(b) && $stable(cout)) |-> $stable(sum)
    );

    // With a and b stable and different, a change in cout must change sum.
    check_sum_changes_when_cout_toggles: assert property (
        @(posedge CLK) ($stable(a) && $stable(b) && (a != b) && $changed(cout)) |-> $changed(sum)
    );

    // If a and b are stable, any change in sum must be due to a change in cout.
    check_sum_change_implies_cout_change: assert property (
        @(posedge CLK) ($stable(a) && $stable(b) && $changed(sum)) |-> $changed(cout)
    );

    // A generate at bit 8 (a[8]&b[8]) forces cout high.
    check_g8_forces_cout: assert property (
        @(posedge CLK) (a[8] & b[8]) |-> cout
    );
endmodule