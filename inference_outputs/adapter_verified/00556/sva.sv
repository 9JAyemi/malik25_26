module my_module_sva (
    input logic clk,
    input logic Z,
    input logic A,
    input logic TE_B
);

// Z must equal A when TE_B is low.
    check_select_a_when_te_b_low: assert property (
        @(posedge clk) !TE_B |-> (Z == A)
    );

// Z must be high when TE_B is high.
    check_te_b_forces_high: assert property (
        @(posedge clk) TE_B |-> (Z == 1'b1)
    );

// A high with TE_B low must drive Z high.
    check_a_high_drives_z_high: assert property (
        @(posedge clk) (!TE_B && A) |-> (Z == 1'b1)
    );

// A low with TE_B low must drive Z low.
    check_a_low_drives_z_low: assert property (
        @(posedge clk) (!TE_B && !A) |-> (Z == 1'b0)
    );

endmodule
