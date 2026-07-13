module and_gate_4_sva (
    input logic clk,   // sampling clock (DUT has no clock/reset)
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic C1,
    input logic Y,
    input logic temp1,
    input logic temp2,
    input logic temp3
);
    // temp1 is A1 & A2.
    check_temp1_and: assert property (
        @(posedge clk) temp1 == (A1 & A2)
    );

    // temp2 is temp1 & A3.
    check_temp2_and: assert property (
        @(posedge clk) temp2 == (temp1 & A3)
    );

    // temp3 is temp2 & B1.
    check_temp3_and: assert property (
        @(posedge clk) temp3 == (temp2 & B1)
    );

    // Y is temp3 & C1.
    check_y_is_temp3_and_c1: assert property (
        @(posedge clk) Y == (temp3 & C1)
    );

    // Y equals A1 & A2 & A3 & B1 & C1.
    check_y_equals_all_inputs: assert property (
        @(posedge clk) Y == (A1 & A2 & A3 & B1 & C1)
    );

    // If Y is HIGH then all inputs are HIGH.
    check_y_high_implies_all_inputs_high: assert property (
        @(posedge clk) (Y == 1'b1) |-> (A1 & A2 & A3 & B1 & C1)
    );

    // If all inputs are HIGH then Y is HIGH.
    check_all_inputs_high_implies_y_high: assert property (
        @(posedge clk) (A1 & A2 & A3 & B1 & C1) |-> (Y == 1'b1)
    );

    // Any LOW input forces Y LOW.
    check_any_input_low_forces_y_low: assert property (
        @(posedge clk) ((!A1) || (!A2) || (!A3) || (!B1) || (!C1)) |-> (Y == 1'b0)
    );
endmodule