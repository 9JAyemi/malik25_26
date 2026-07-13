module top_module_sva (
    input logic a,
    input logic b,
    input logic pipe1,
    input logic pipe2,
    input logic out,
    input logic g1_pipe1,
    input logic g2_pipe1,
    input logic g3_pipe1
);

    // Primary input changes update g1's first stage to ~(a & b).
    check_g1_input_updates_first_stage: assert property (
        @($global_clock) (!$initstate && ($changed(a) || $changed(b))) |-> (g1_pipe1 == ~(a & b))
    );

    // A g1 first-stage change updates the top-level pipe1 output to ~g1_pipe1.
    check_g1_first_stage_updates_pipe1: assert property (
        @($global_clock) (!$initstate && $changed(g1_pipe1)) |-> (pipe1 == ~g1_pipe1)
    );

    // A pipe1 change updates g2's first stage to ~(pipe1 & pipe1).
    check_g2_input_updates_first_stage: assert property (
        @($global_clock) (!$initstate && $changed(pipe1)) |-> (g2_pipe1 == ~(pipe1 & pipe1))
    );

    // A g2 first-stage change updates the top-level pipe2 output to ~g2_pipe1.
    check_g2_first_stage_updates_pipe2: assert property (
        @($global_clock) (!$initstate && $changed(g2_pipe1)) |-> (pipe2 == ~g2_pipe1)
    );

    // A pipe2 change updates g3's first stage to ~(pipe2 & pipe2).
    check_g3_input_updates_first_stage: assert property (
        @($global_clock) (!$initstate && $changed(pipe2)) |-> (g3_pipe1 == ~(pipe2 & pipe2))
    );

    // A g3 first-stage change updates out to ~g3_pipe1.
    check_g3_first_stage_updates_out: assert property (
        @($global_clock) (!$initstate && $changed(g3_pipe1)) |-> (out == ~g3_pipe1)
    );

endmodule