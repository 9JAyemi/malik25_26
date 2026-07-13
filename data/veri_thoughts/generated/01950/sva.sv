module behavioral_sva (
    input logic clk,     // sampling clock for SVA (RTL has no clock/reset)
    input logic out,
    input logic a,
    input logic b,
    input logic e,
    input logic w
);
    // RTL is purely combinational; out implements (~a & ~b), e/w are don't-cares.

    // out must equal (~a & ~b) every cycle.
    check_function_equivalence: assert property (
        @(posedge clk) out == ((~a) & (~b))
    );

    // When a=0 and b=0, out must be 1.
    check_out_high_when_a0_b0: assert property (
        @(posedge clk) (!a && !b) |-> (out == 1'b1)
    );

    // When a=1 and b=0, out must be 0.
    check_out_low_when_a1_b0: assert property (
        @(posedge clk) (a && !b) |-> (out == 1'b0)
    );

    // When a=0 and b=1, out must be 0.
    check_out_low_when_a0_b1: assert property (
        @(posedge clk) (!a && b) |-> (out == 1'b0)
    );

    // When a=1 and b=1, out must be 0.
    check_out_low_when_a1_b1: assert property (
        @(posedge clk) (a && b) |-> (out == 1'b0)
    );

    // Enumerated case: ~a & ~b & ~e & ~w -> out=1.
    check_case_a0_b0_e0_w0: assert property (
        @(posedge clk) (!a && !b && !e && !w) |-> (out == 1'b1)
    );

    // Enumerated case: ~a & ~b & e & w -> out=1.
    check_case_a0_b0_e1_w1: assert property (
        @(posedge clk) (!a && !b && e && w) |-> (out == 1'b1)
    );

    // Enumerated case: ~a & b & e & w -> out=0.
    check_case_a0_b1_e1_w1: assert property (
        @(posedge clk) (!a && b && e && w) |-> (out == 1'b0)
    );

    // Enumerated case: a & ~b & e & w -> out=0.
    check_case_a1_b0_e1_w1: assert property (
        @(posedge clk) (a && !b && e && w) |-> (out == 1'b0)
    );

    // Enumerated case: a & b & e & w -> out=0.
    check_case_a1_b1_e1_w1: assert property (
        @(posedge clk) (a && b && e && w) |-> (out == 1'b0)
    );
endmodule