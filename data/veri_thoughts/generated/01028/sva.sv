module sky130_fd_sc_hd__a41oi_sva (
    input logic CLK,   // sampling clock for assertions
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic A4,
    input logic B1
);
    // Y equals ~(B1 | (A1&A2&A3&A4)).
    check_function_equivalence: assert property (
        @(posedge CLK) Y === ~(B1 | (A1 & A2 & A3 & A4))
    );

    // B1=1 forces Y=0.
    check_b1_high_forces_y_low: assert property (
        @(posedge CLK) (B1 === 1'b1) |-> (Y === 1'b0)
    );

    // All A inputs high force Y=0.
    check_all_as_high_forces_y_low: assert property (
        @(posedge CLK) ((A1 & A2 & A3 & A4) === 1'b1) |-> (Y === 1'b0)
    );

    // B1=0 and not all As high force Y=1.
    check_b1_low_and_any_a_low_forces_y_high: assert property (
        @(posedge CLK) ((B1 === 1'b0) && ((A1 & A2 & A3 & A4) === 1'b0)) |-> (Y === 1'b1)
    );

    // Y=1 implies B1=0 and not all As high.
    check_y_high_implies_inputs: assert property (
        @(posedge CLK) (Y === 1'b1) |-> ((B1 === 1'b0) && ((A1 & A2 & A3 & A4) === 1'b0))
    );

    // Y=0 and B1=0 imply all As high.
    check_y_low_and_b1_low_implies_all_as_high: assert property (
        @(posedge CLK) ((Y === 1'b0) && (B1 === 1'b0)) |-> ((A1 & A2 & A3 & A4) === 1'b1)
    );

    // Y=0 and not all As high imply B1=1.
    check_y_low_and_and4_low_implies_b1_high: assert property (
        @(posedge CLK) ((Y === 1'b0) && ((A1 & A2 & A3 & A4) === 1'b0)) |-> (B1 === 1'b1)
    );

    // If inputs are stable, Y is stable.
    check_input_stability_implies_y_stability: assert property (
        @(posedge CLK) $stable({A1, A2, A3, A4, B1}) |-> $stable(Y)
    );

    // Y rising requires B1=0 and not all As high.
    check_y_rise_requires_conditions: assert property (
        @(posedge CLK) $rose(Y) |-> ((B1 === 1'b0) && ((A1 & A2 & A3 & A4) === 1'b0))
    );

    // Y falling requires B1=1 or all As high.
    check_y_fall_requires_conditions: assert property (
        @(posedge CLK) $fell(Y) |-> ((B1 === 1'b1) || ((A1 & A2 & A3 & A4) === 1'b1))
    );
endmodule