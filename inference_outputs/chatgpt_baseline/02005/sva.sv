module sky130_fd_sc_lp__iso0p_sva (
    input logic X,
    input logic A,
    input logic SLEEP
);
    // X must equal A & ~SLEEP (functional definition).
    check_functional_equivalence: assert property (
        @(posedge A or negedge A or posedge SLEEP or negedge SLEEP) X === (A & ~SLEEP)
    );

    // When SLEEP is 1, X must be 0 (isolation active).
    check_iso_forced_low: assert property (
        @(posedge A or negedge A or posedge SLEEP or negedge SLEEP) (SLEEP === 1'b1) |-> (X === 1'b0)
    );

    // When SLEEP is 0, X passes A.
    check_pass_through_when_awake: assert property (
        @(posedge A or negedge A or posedge SLEEP or negedge SLEEP) (SLEEP === 1'b0) |-> (X === A)
    );

    // If A is 0, X must be 0 regardless of SLEEP.
    check_zero_when_A_zero: assert property (
        @(posedge A or negedge A or posedge SLEEP or negedge SLEEP) (A === 1'b0) |-> (X === 1'b0)
    );

    // X can be 1 only when A is 1 and SLEEP is 0.
    check_one_only_when_A1_and_awake: assert property (
        @(posedge A or negedge A or posedge SLEEP or negedge SLEEP) (X === 1'b1) |-> ((A === 1'b1) && (SLEEP === 1'b0))
    );
endmodule