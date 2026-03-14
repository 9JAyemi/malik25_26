module synch_3_sva #(parameter WIDTH = 1) (
    input  logic             clk,
    input  logic [WIDTH-1:0] i,
    input  logic [WIDTH-1:0] o,
    input  logic [WIDTH-1:0] stage_1,
    input  logic [WIDTH-1:0] stage_2,
    input  logic [WIDTH-1:0] stage_3
);
    // stage_1 captures i with 1-cycle latency.
    capture_stage1_from_i: assert property (
        @(posedge clk) $past(1'b1) |-> (stage_1 == $past(i))
    );

    // stage_2 captures stage_1 with 1-cycle latency.
    capture_stage2_from_stage1: assert property (
        @(posedge clk) $past(1'b1) |-> (stage_2 == $past(stage_1))
    );

    // stage_3 captures stage_2 with 1-cycle latency.
    capture_stage3_from_stage2: assert property (
        @(posedge clk) $past(1'b1) |-> (stage_3 == $past(stage_2))
    );

    // o captures stage_3 with 1-cycle latency.
    capture_o_from_stage3: assert property (
        @(posedge clk) $past(1'b1) |-> (o == $past(stage_3))
    );

    // stage_2 equals i delayed by 2 cycles.
    stage2_equals_i_delayed2: assert property (
        @(posedge clk) $past(1'b1,2) |-> (stage_2 == $past(i,2))
    );

    // stage_3 equals i delayed by 3 cycles.
    stage3_equals_i_delayed3: assert property (
        @(posedge clk) $past(1'b1,3) |-> (stage_3 == $past(i,3))
    );

    // o equals i delayed by 4 cycles.
    o_equals_i_delayed4: assert property (
        @(posedge clk) $past(1'b1,4) |-> (o == $past(i,4))
    );

    // stage_3 equals stage_1 delayed by 2 cycles.
    stage3_equals_stage1_delayed2: assert property (
        @(posedge clk) $past(1'b1,2) |-> (stage_3 == $past(stage_1,2))
    );

    // o equals stage_2 delayed by 2 cycles.
    o_equals_stage2_delayed2: assert property (
        @(posedge clk) $past(1'b1,2) |-> (o == $past(stage_2,2))
    );

    // If i changes, o reflects that value exactly 4 cycles later.
    latency_4_on_i_change_to_o: assert property (
        @(posedge clk) $changed(i) |=> ##3 (o == $past(i,4))
    );
endmodule