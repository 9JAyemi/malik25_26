module sky130_fd_sc_ls__nor3_sva (
    input logic Y,
    input logic A,
    input logic B,
    input logic C
);
    // Y equals bitwise NOR of A, B, C.
    check_nor_functional_equivalence: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge Y or negedge Y)
            (Y === ~(A | B | C))
    );

    // A HIGH forces Y LOW.
    check_A_high_forces_Y_low: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge Y or negedge Y)
            (A === 1'b1) |-> (Y === 1'b0)
    );

    // B HIGH forces Y LOW.
    check_B_high_forces_Y_low: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge Y or negedge Y)
            (B === 1'b1) |-> (Y === 1'b0)
    );

    // C HIGH forces Y LOW.
    check_C_high_forces_Y_low: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge Y or negedge Y)
            (C === 1'b1) |-> (Y === 1'b0)
    );

    // All inputs LOW force Y HIGH.
    check_all_inputs_low_forces_Y_high: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge Y or negedge Y)
            ((A === 1'b0) && (B === 1'b0) && (C === 1'b0)) |-> (Y === 1'b1)
    );

    // Y HIGH implies all inputs are LOW.
    check_Y_high_implies_all_inputs_low: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge Y or negedge Y)
            (Y === 1'b1) |-> ((A === 1'b0) && (B === 1'b0) && (C === 1'b0))
    );

    // Y LOW implies at least one input is HIGH.
    check_Y_low_implies_any_input_high: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge Y or negedge Y)
            (Y === 1'b0) |-> ((A === 1'b1) || (B === 1'b1) || (C === 1'b1))
    );
endmodule