module complement_module_sva (
    input logic clk,
    input logic [3:0] in_vec,
    input logic sel_comp,
    input logic [3:0] outv,
    input logic [3:0] complement
);

    // outv is a direct pass-through of in_vec.
    check_outv_passthrough: assert property (
        @(posedge clk) outv == in_vec
    );

    // complement matches the RTL's selected complement function.
    check_complement_exact_function: assert property (
        @(posedge clk) complement == ((sel_comp == 1'b1) ? (~in_vec + 4'b0001) : ~in_vec)
    );

    // sel_comp low selects ones' complement.
    check_ones_complement_when_not_selected: assert property (
        @(posedge clk) (sel_comp == 1'b0) |-> (complement == ~in_vec)
    );

    // sel_comp high selects twos' complement.
    check_twos_complement_when_selected: assert property (
        @(posedge clk) (sel_comp == 1'b1) |-> (complement == (~in_vec + 4'b0001))
    );

    // Ones' complement output is the bitwise inverse of the input.
    check_ones_complement_inverse_relation: assert property (
        @(posedge clk) (sel_comp == 1'b0) |-> ((complement ^ in_vec) == 4'hF)
    );

    // Twos' complement output adds with the input to zero modulo 16.
    check_twos_complement_additive_inverse: assert property (
        @(posedge clk) (sel_comp == 1'b1) |-> ((complement + in_vec) == 4'b0000)
    );

endmodule