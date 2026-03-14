module sky130_fd_sc_hdll__or4b_sva (
    input  logic CLK,
    input  logic X,
    input  logic A,
    input  logic B,
    input  logic C,
    input  logic D_N
);
    // X equals A OR B OR C OR (~D_N).
    check_func_equiv: assert property (
        @(posedge CLK) X === (A | B | C | ~D_N)
    );

    // If A is 1 then X is 1.
    check_a_one_implies_x_one: assert property (
        @(posedge CLK) (A === 1'b1) |-> (X === 1'b1)
    );

    // If B is 1 then X is 1.
    check_b_one_implies_x_one: assert property (
        @(posedge CLK) (B === 1'b1) |-> (X === 1'b1)
    );

    // If C is 1 then X is 1.
    check_c_one_implies_x_one: assert property (
        @(posedge CLK) (C === 1'b1) |-> (X === 1'b1)
    );

    // If D_N is 0 then X is 1.
    check_dn_zero_implies_x_one: assert property (
        @(posedge CLK) (D_N === 1'b0) |-> (X === 1'b1)
    );

    // If A,B,C are 0 and D_N is 1 then X is 0.
    check_all_zero_and_dn_one_implies_x_zero: assert property (
        @(posedge CLK) ((A === 1'b0) && (B === 1'b0) && (C === 1'b0) && (D_N === 1'b1)) |-> (X === 1'b0)
    );

    // If X is 0 then A,B,C are 0 and D_N is 1.
    check_x_zero_implies_inputs_zero_dn_one: assert property (
        @(posedge CLK) (X === 1'b0) |-> ((A === 1'b0) && (B === 1'b0) && (C === 1'b0) && (D_N === 1'b1))
    );

    // If X is 1 and D_N is 1 then at least one of A,B,C is 1.
    check_x_one_dn_one_requires_abc_one: assert property (
        @(posedge CLK) ((X === 1'b1) && (D_N === 1'b1)) |-> ((A === 1'b1) || (B === 1'b1) || (C === 1'b1))
    );

    // If X is 1 and A,B,C are 0 then D_N is 0.
    check_x_one_with_abc_zero_requires_dn_zero: assert property (
        @(posedge CLK) ((X === 1'b1) && (A === 1'b0) && (B === 1'b0) && (C === 1'b0)) |-> (D_N === 1'b0)
    );

    // If A,B,C are 0 then X equals ~D_N.
    check_abc_zero_links_x_to_not_dn: assert property (
        @(posedge CLK) ((A === 1'b0) && (B === 1'b0) && (C === 1'b0)) |-> (X === (~D_N))
    );

    // If D_N is 1 then X equals A|B|C.
    check_dn_one_links_x_to_abc_or: assert property (
        @(posedge CLK) (D_N === 1'b1) |-> (X === (A | B | C))
    );
endmodule