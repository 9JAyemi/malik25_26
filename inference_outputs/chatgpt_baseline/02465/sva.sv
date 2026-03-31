module my_module_sva (
    input logic clk,      // sampling clock for assertions (DUT has no clock)
    input logic rst_n,    // active-low assertion reset (DUT has no reset)
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1
);
    // X equals the RTL Boolean expression.
    check_x_definition: assert property (
        @(posedge clk) disable iff (!rst_n)
        X == ((A1 & ~A2) | (A2 & ~A1 & A3 & ~B1) | (~A1 & ~A2 & ~A3 & B1))
    );

    // When (A1 & ~A2) holds, X must be 1.
    check_term1_drives_x1: assert property (
        @(posedge clk) disable iff (!rst_n)
        (A1 & ~A2) |-> (X == 1'b1)
    );

    // When (A2 & ~A1 & A3 & ~B1) holds, X must be 1.
    check_term2_drives_x1: assert property (
        @(posedge clk) disable iff (!rst_n)
        (A2 & ~A1 & A3 & ~B1) |-> (X == 1'b1)
    );

    // When (~A1 & ~A2 & ~A3 & B1) holds, X must be 1.
    check_term3_drives_x1: assert property (
        @(posedge clk) disable iff (!rst_n)
        (~A1 & ~A2 & ~A3 & B1) |-> (X == 1'b1)
    );

    // If none of the three terms holds, X must be 0.
    check_none_terms_implies_x0: assert property (
        @(posedge clk) disable iff (!rst_n)
        ~((A1 & ~A2) | (A2 & ~A1 & A3 & ~B1) | (~A1 & ~A2 & ~A3 & B1)) |-> (X == 1'b0)
    );

    // If X is 1, at least one of the three terms must hold.
    check_x1_implies_some_term: assert property (
        @(posedge clk) disable iff (!rst_n)
        (X == 1'b1) |-> ((A1 & ~A2) | (A2 & ~A1 & A3 & ~B1) | (~A1 & ~A2 & ~A3 & B1))
    );

    // With inputs stable across a cycle, X must remain stable (pure combinational).
    check_stable_inputs_hold_x_stable: assert property (
        @(posedge clk) disable iff (!rst_n)
        $stable({A1, A2, A3, B1}) |-> $stable(X)
    );
endmodule