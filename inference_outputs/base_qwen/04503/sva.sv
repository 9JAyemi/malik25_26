```systemverilog
module sky130_fd_sc_hd__fah_sva (
    input logic CLK,
    input logic RESETn,
    input logic A,
    input logic B,
    input logic CI,
    output logic COUT,
    output logic SUM
);
    // XOR operation between A, B, and CI
    xor_operation: assert property (
        @(posedge CLK) disable iff (!RESETn) (SUM == A ^ B ^ CI)
    );

    // OR operation between A and B
    or_operation: assert property (
        @(posedge CLK) disable iff (!RESETn) (A_b == A | B)
    );

    // AND operation between A and CI
    and_operation_A: assert property (
        @(posedge CLK) disable iff (!RESETn) (A_ci == A & CI)
    );

    // AND operation between B and CI
    and_operation_B: assert property (
        @(posedge CLK) disable iff (!RESETn) (B_ci == B & CI)
    );

    // OR operation between A_b, A_ci, and B_ci
    or_operation_COUT: assert property (
        @(posedge CLK) disable iff (!RESETn) (COUT == A_b | A_ci | B_ci)
    );

    // Device reset behavior
    reset_behavior: assert property (
        @(posedge CLK) !RESETn |-> (SUM == 1'b0) && (COUT == 1'b0)
    );

endmodule
```