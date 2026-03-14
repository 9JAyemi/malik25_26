module decoder_3to8_sva (
    // DUT ports
    input logic A,
    input logic B,
    input logic C,
    input logic Y0,
    input logic Y1,
    input logic Y2,
    input logic Y3,
    input logic Y4,
    input logic Y5,
    input logic Y6,
    input logic Y7,
    // Sampling clock for SVA (RTL has no clock/reset)
    input logic clk
);
    // No clock/reset in RTL; assertions are sampled on clk without reset gating.
    // Purely combinational 3-to-8 decoder: Y[i] is one-hot minterm of A,B,C.

    // Y0 equals ~(A | B | C)
    check_y0_definition: assert property (
        @(posedge clk) Y0 == ~(A | B | C)
    );

    // Y1 equals ~(A | B | ~C)
    check_y1_definition: assert property (
        @(posedge clk) Y1 == ~(A | B | ~C)
    );

    // Y2 equals ~(A | ~B | C)
    check_y2_definition: assert property (
        @(posedge clk) Y2 == ~(A | ~B | C)
    );

    // Y3 equals ~(A | ~B | ~C)
    check_y3_definition: assert property (
        @(posedge clk) Y3 == ~(A | ~B | ~C)
    );

    // Y4 equals ~(~A | B | C)
    check_y4_definition: assert property (
        @(posedge clk) Y4 == ~(~A | B | C)
    );

    // Y5 equals ~(~A | B | ~C)
    check_y5_definition: assert property (
        @(posedge clk) Y5 == ~(~A | B | ~C)
    );

    // Y6 equals ~(~A | ~B | C)
    check_y6_definition: assert property (
        @(posedge clk) Y6 == ~(~A | ~B | C)
    );

    // Y7 equals ~(~A | ~B | ~C)
    check_y7_definition: assert property (
        @(posedge clk) Y7 == ~(~A | ~B | ~C)
    );

    // Exactly one output is HIGH for any A,B,C
    check_onehot_outputs: assert property (
        @(posedge clk) $onehot({Y7,Y6,Y5,Y4,Y3,Y2,Y1,Y0})
    );

    // Outputs cover all cases (OR of all Y is 1)
    check_outputs_cover_all: assert property (
        @(posedge clk) (|{Y7,Y6,Y5,Y4,Y3,Y2,Y1,Y0}) == 1'b1
    );

    // If inputs are stable, outputs remain stable (combinational behavior)
    check_output_stability_when_inputs_stable: assert property (
        @(posedge clk) $stable({A,B,C}) |-> $stable({Y7,Y6,Y5,Y4,Y3,Y2,Y1,Y0})
    );
endmodule