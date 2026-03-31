module arithmetic_module_sva (
    input logic clk,
    input logic Boo_ba1,
    input logic Boo_ba2,
    input logic b,
    input logic Boo_ba3,
    input logic c,
    input logic [3:0] f4_dotnamed
);

    // f4 is the sum of the three sub-block outputs.
    check_f4_sum: assert property (
        @(posedge clk)
        f4_dotnamed == ((Boo_ba1 << 1) + (Boo_ba2 + b) + (Boo_ba3 - c))
    );

    // The SubA contribution is the left-shifted Boo_ba1 value.
    check_suba_contribution: assert property (
        @(posedge clk)
        f4_dotnamed[3:1] == (Boo_ba1 << 1)
    );

    // The SubB contribution is the low 3 bits of Boo_ba2 plus b.
    check_subb_contribution: assert property (
        @(posedge clk)
        f4_dotnamed[2:0] == (Boo_ba2 + b)[2:0]
    );

    // The SubC contribution is the low 3 bits of Boo_ba3 minus c.
    check_subc_contribution: assert property (
        @(posedge clk)
        f4_dotnamed[2:0] == (Boo_ba3 - c)[2:0]
    );

    // Stable inputs keep the combinational output stable.
    check_stable_inputs_stable_output: assert property (
        @(posedge clk)
        $stable({Boo_ba1, Boo_ba2, b, Boo_ba3, c}) |-> $stable(f4_dotnamed)
    );

    // Changing only Boo_ba1 changes only the SubA contribution.
    check_boob_a1_changes_only_suba: assert property (
        @(posedge clk)
        $changed(Boo_ba1) && $stable({Boo_ba2, b, Boo_ba3, c}) |-> (
            $changed(f4_dotnamed[3:1]) &&
            $stable(f4_dotnamed[2:0])
        )
    );

    // Changing only Boo_ba2 changes only the SubB contribution.
    check_boob_a2_changes_only_subb: assert property (
        @(posedge clk)
        $changed(Boo_ba2) && $stable({Boo_ba1, b, Boo_ba3, c}) |-> (
            $changed(f4_dotnamed[2:0]) &&
            $stable(f4_dotnamed[3:1])
        )
    );

    // Changing only b changes only the SubB contribution.
    check_b_changes_only_subb: assert property (
        @(posedge clk)
        $changed(b) && $stable({Boo_ba1, Boo_ba2, Boo_ba3, c}) |-> (
            $changed(f4_dotnamed[2:0]) &&
            $stable(f4_dotnamed[3:1])
        )
    );

    // Changing only Boo_ba3 changes only the SubC contribution.
    check_boob_a3_changes_only_subc: assert property (
        @(posedge clk)
        $changed(Boo_ba3) && $stable({Boo_ba1, Boo_ba2, b, c}) |-> (
            $changed(f4_dotnamed[2:0]) &&
            $stable(f4_dotnamed[3:1])
        )
    );

    // Changing only c changes only the SubC contribution.
    check_c_changes_only_subc: assert property (
        @(posedge clk)
        $changed(c) && $stable({Boo_ba1, Boo_ba2, b, Boo_ba3}) |-> (
            $changed(f4_dotnamed[2:0]) &&
            $stable(f4_dotnamed[3:1])
        )
    );

endmodule