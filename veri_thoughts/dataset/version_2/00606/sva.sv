module top_module_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1
);
    ///// Functional correctness /////
    // Y equals ~((A1 & A2 & A3) | B1).
    check_function_equation: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge A3 or negedge A3 or
          posedge B1 or negedge B1)
        Y == ~((A1 & A2 & A3) | B1)
    );

    // If Y is HIGH, B1 must be LOW and at least one Ai is LOW.
    check_y_high_requires_inputs: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge A3 or negedge A3 or
          posedge B1 or negedge B1)
        (Y == 1'b1) |-> ((B1 == 1'b0) && ((A1 == 1'b0) || (A2 == 1'b0) || (A3 == 1'b0)))
    );

    // If B1 is LOW and at least one Ai is LOW, Y must be HIGH.
    check_inputs_imply_y_high: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge A3 or negedge A3 or
          posedge B1 or negedge B1)
        ((B1 == 1'b0) && ((A1 == 1'b0) || (A2 == 1'b0) || (A3 == 1'b0))) |-> (Y == 1'b1)
    );

    // If B1 is HIGH, Y must be LOW.
    check_b1_high_forces_y_low: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge A3 or negedge A3 or
          posedge B1 or negedge B1)
        (B1 == 1'b1) |-> (Y == 1'b0)
    );

    // If all A inputs are HIGH, Y must be LOW.
    check_all_a_high_forces_y_low: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge A3 or negedge A3 or
          posedge B1 or negedge B1)
        ((A1 == 1'b1) && (A2 == 1'b1) && (A3 == 1'b1)) |-> (Y == 1'b0)
    );

    // Y and B1 cannot both be HIGH.
    check_y_and_b1_mutex: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge A3 or negedge A3 or
          posedge B1 or negedge B1)
        !(Y && B1)
    );
endmodule