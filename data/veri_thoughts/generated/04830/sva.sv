module my_module_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic E,
    input logic Z
);

    // Z implements (A&B) | (C&D) | E.
    check_output_function: assert property (
        @(posedge clk) Z == ((A & B) | (C & D) | E)
    );

    // E high must force Z high.
    check_e_term_drives_z: assert property (
        @(posedge clk) E |-> Z
    );

    // A and B high must force Z high.
    check_ab_term_drives_z: assert property (
        @(posedge clk) (A & B) |-> Z
    );

    // C and D high must force Z high.
    check_cd_term_drives_z: assert property (
        @(posedge clk) (C & D) |-> Z
    );

    // If all three OR terms are low, Z must be low.
    check_no_active_term_means_z_low: assert property (
        @(posedge clk) (!(A & B) && !(C & D) && !E) |-> !Z
    );

    // If Z is low, none of the three OR terms can be high.
    check_z_low_implies_no_active_term: assert property (
        @(posedge clk) !Z |-> (!(A & B) && !(C & D) && !E)
    );

endmodule