module shift_register_sva (
    input logic clk,
    input logic [3:0] data_in,
    input logic shift_right,
    input logic load,
    input logic [3:0] data_out,
    input logic [3:0] stage1,
    input logic [3:0] stage2,
    input logic [3:0] stage3,
    input logic [3:0] stage4
);
    // data_out always mirrors stage4.
    check_data_out_mirrors_stage4: assert property (
        @(posedge clk) data_out === stage4
    );

    // On load, next stage1 captures data_in.
    check_load_stage1_from_data_in: assert property (
        @(posedge clk) load |-> (stage1 === $past(data_in))
    );
    // On load, next stage2 captures prior stage1.
    check_load_stage2_from_stage1: assert property (
        @(posedge clk) load |-> (stage2 === $past(stage1))
    );
    // On load, next stage3 captures prior stage2.
    check_load_stage3_from_stage2: assert property (
        @(posedge clk) load |-> (stage3 === $past(stage2))
    );
    // On load, next stage4 captures prior stage3.
    check_load_stage4_from_stage3: assert property (
        @(posedge clk) load |-> (stage4 === $past(stage3))
    );

    // On shift_right (no load), next stage1 captures prior stage4.
    check_shr_stage1_from_stage4: assert property (
        @(posedge clk) (!load && shift_right) |-> (stage1 === $past(stage4))
    );
    // On shift_right (no load), next stage2 captures prior stage1.
    check_shr_stage2_from_stage1: assert property (
        @(posedge clk) (!load && shift_right) |-> (stage2 === $past(stage1))
    );
    // On shift_right (no load), next stage3 captures prior stage2.
    check_shr_stage3_from_stage2: assert property (
        @(posedge clk) (!load && shift_right) |-> (stage3 === $past(stage2))
    );
    // On shift_right (no load), next stage4 captures prior stage3.
    check_shr_stage4_from_stage3: assert property (
        @(posedge clk) (!load && shift_right) |-> (stage4 === $past(stage3))
    );

    // On shift_left path (no load and no shift_right), next stage1 captures prior stage2.
    check_shl_stage1_from_stage2: assert property (
        @(posedge clk) (!load && !shift_right) |-> (stage1 === $past(stage2))
    );
    // On shift_left path (no load and no shift_right), next stage2 captures prior stage3.
    check_shl_stage2_from_stage3: assert property (
        @(posedge clk) (!load && !shift_right) |-> (stage2 === $past(stage3))
    );
    // On shift_left path (no load and no shift_right), next stage3 captures prior stage4.
    check_shl_stage3_from_stage4: assert property (
        @(posedge clk) (!load && !shift_right) |-> (stage3 === $past(stage4))
    );
    // On shift_left path (no load and no shift_right), next stage4 captures data_in.
    check_shl_stage4_from_data_in: assert property (
        @(posedge clk) (!load && !shift_right) |-> (stage4 === $past(data_in))
    );
endmodule