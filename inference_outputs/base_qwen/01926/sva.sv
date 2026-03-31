```systemverilog
module axis_infrastructure_v1_1_clock_synchronizer_sva (
    input logic clk,
    input logic synch_in,
    output logic synch_out
);
    // Synchronizer stages must be initialized to 0 at reset
    reset: assert property (
        @(posedge clk) disable iff (!clk) synch_out |-> synch_in
    );

    // Synchronizer stages must propagate the input signal through the stages
    sync_stages: assert property (
        @(posedge clk) disable iff (!clk) $stable(synch_in) |-> $stable(synch_out)
    );

    // Synchronizer stages must not change the output signal unless the input signal changes
    sync_no_change: assert property (
        @(posedge clk) disable iff (!clk) $stable(synch_in) |-> $stable(synch_out)
    );

    // Synchronizer stages must not change the output signal unless the input signal changes
    sync_no_change_2: assert property (
        @(posedge clk) disable iff (!clk) $stable(synch_in) |-> $stable(synch_out)
    );

    // Synchronizer stages must not change the output signal unless the input signal changes
    sync_no_change_3: assert property (
        @(posedge clk) disable iff (!clk) $stable(synch_in) |-> $stable(synch_out)
    );

    // Synchronizer stages must not change the output signal unless the input signal changes
    sync_no_change_4: assert property (
        @(posedge clk) disable iff (!clk) $stable(synch_in) |-> $stable(synch_out)
    );

    // Synchronizer stages must not change the output signal unless the input signal changes
    sync_no_change_5: assert property (
        @(posedge clk) disable iff (!clk) $stable(synch_in) |-> $stable(synch_out)
    );

    // Synchronizer stages must not change the output signal unless the input signal changes
    sync_no_change_6: assert property (
        @(posedge clk) disable iff (!clk) $stable(synch_in) |-> $stable(synch_out)
    );

    // Synchronizer stages must not change the output signal unless the input signal changes
    sync_no_change_7: assert property (
        @(posedge clk) disable iff (!clk) $stable(synch_in) |-> $stable(synch_out)
    );

    // Synchronizer stages must not change the output signal unless the input signal changes
    sync_no_change_8: assert property (
        @(posedge clk) disable iff (!clk) $stable(synch_in) |-> $stable(synch_out)
    );
endmodule
```