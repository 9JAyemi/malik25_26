module my_module_sva (
    input logic A,
    input logic TE,
    input logic VPWR,
    input logic VGND,
    input logic Z
);
    // No clock/reset in RTL; pure combinational logic sampled on input edges.

    // When A=1 and TE=0, Z must equal VPWR.
    check_a1_te0: assert property (
        @(posedge A or negedge A or posedge TE or negedge TE or posedge VPWR or negedge VPWR or posedge VGND or negedge VGND)
        (A && !TE) |=> (Z == VPWR)
    );

    // When A=0 and TE=1, Z must equal VGND.
    check_a0_te1: assert property (
        @(posedge A or negedge A or posedge TE or negedge TE or posedge VPWR or negedge VPWR or posedge VGND or negedge VGND)
        (!A && TE) |=> (Z == VGND)
    );

    // When A=1 and TE=1, Z must be 1.
    check_a1_te1: assert property (
        @(posedge A or negedge A or posedge TE or negedge TE or posedge VPWR or negedge VPWR or posedge VGND or negedge VGND)
        (A && TE) |=> (Z == 1'b1)
    );

    // When A=0 and TE=0, Z must be 0.
    check_a0_te0: assert property (
        @(posedge A or negedge A or posedge TE or negedge TE or posedge VPWR or negedge VPWR or posedge VGND or negedge VGND)
        (!A && !TE) |=> (Z == 1'b0)
    );

    // Summary for TE=0: Z equals (A ? VPWR : 0).
    check_te0_summary: assert property (
        @(posedge A or negedge A or posedge TE or negedge TE or posedge VPWR or negedge VPWR or posedge VGND or negedge VGND)
        (!TE) |=> (Z == (A ? VPWR : 1'b0))
    );

    // Summary for TE=1: Z equals (A ? 1 : VGND).
    check_te1_summary: assert property (
        @(posedge A or negedge A or posedge TE or negedge TE or posedge VPWR or negedge VPWR or posedge VGND or negedge VGND)
        (TE) |=> (Z == (A ? 1'b1 : VGND))
    );

    // When A and TE are equal, Z must equal TE (covers both 00->0 and 11->1).
    check_equal_inputs: assert property (
        @(posedge A or negedge A or posedge TE or negedge TE or posedge VPWR or negedge VPWR or posedge VGND or negedge VGND)
        (A == TE) |=> (Z == TE)
    );

    // Exact functional mapping: Z matches the coded truth table.
    check_truth_table_function: assert property (
        @(posedge A or negedge A or posedge TE or negedge TE or posedge VPWR or negedge VPWR or posedge VGND or negedge VGND)
        1'b1 |=> (Z == ((A && !TE) ? VPWR :
                        ((!A) && TE) ? VGND :
                        (A && TE)   ? 1'b1  :
                                      1'b0))
    );

endmodule