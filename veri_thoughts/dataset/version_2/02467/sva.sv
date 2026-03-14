module sky130_fd_sc_ms__bufinv_sva (
    input logic Y,
    input logic A
);
    // Y is the logical inversion of A whenever either signal changes.
    check_inversion_on_change: assert property (
        @(posedge A or negedge A or posedge Y or negedge Y) (Y === ~A)
    );

    // When A is 0, Y must be 1.
    check_y_high_if_a_low: assert property (
        @(posedge A or negedge A or posedge Y or negedge Y) (A === 1'b0) |-> (Y === 1'b1)
    );

    // When A is 1, Y must be 0.
    check_y_low_if_a_high: assert property (
        @(posedge A or negedge A or posedge Y or negedge Y) (A === 1'b1) |-> (Y === 1'b0)
    );

    // When Y is 0, A must be 1.
    check_a_high_if_y_low: assert property (
        @(posedge A or negedge A or posedge Y or negedge Y) (Y === 1'b0) |-> (A === 1'b1)
    );

    // When Y is 1, A must be 0.
    check_a_low_if_y_high: assert property (
        @(posedge A or negedge A or posedge Y or negedge Y) (Y === 1'b1) |-> (A === 1'b0)
    );
endmodule