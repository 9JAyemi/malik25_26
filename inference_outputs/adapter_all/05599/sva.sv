module rotation_module_sva (
    input logic clk,
    input logic reset,
    input logic [3:0] in,
    input logic load,
    input logic select,
    input logic [15:0] data,
    input logic [3:0] out
);
    // Reset drives out to zero on the next clock.
    reset_clears_out_next: assert property (
        @(posedge clk) reset |=> (out == 4'b0000)
    );

    // With load asserted, out captures data[3:0] on the next clock.
    load_captures_data: assert property (
        @(posedge clk) disable iff (reset) load |=> (out == $past(data[3:0]))
    );

    // With select asserted and load deasserted, out captures {in[2:0], in[3]}.
    select_captures_rotated_in: assert property (
        @(posedge clk) disable iff (reset) (!load && select) |=> (out == { $past(in[2:0]), $past(in[3]) })
    );

    // With neither load nor select asserted, out captures {in[0], in[3:1]}.
    rotate_left_captures_in: assert property (
        @(posedge clk) disable iff (reset) (!load && !select) |=> (out == { $past(in[0]), $past(in[3:1]) })
    );

    // With both load and select asserted, load has priority and data[3:0] is captured.
    load_priority_over_select: assert property (
        @(posedge clk) disable iff (reset) (load && select) |=> (out == $past(data[3:0]))
    );

    // With neither load nor select asserted and in stable, out remains stable.
    stable_when_no_ctrl_and_in_stable: assert property (
        @(posedge clk) disable iff (reset) (!load && !select && $stable(in)) |-> $stable(out)
    );

    // With neither load nor select asserted and in changing, out changes accordingly.
    change_when_no_ctrl_and_in_changes: assert property (
        @(posedge clk) disable iff (reset) (!load && !select && !$stable(in)) |-> !$stable(out)
    );

    // With select asserted and in stable, out remains stable.
    stable_when_select_and_in_stable: assert property (
        @(posedge clk) disable iff (reset) (!load && select && $stable(in)) |-> $stable(out)
    );

    // With select asserted and in changing, out changes accordingly.
    change_when_select_and_in_changes: assert property (
        @(posedge clk) disable iff (reset) (!load && select && !$stable(in)) |-> !$stable(out)
    );

    // With load asserted and data stable, out remains stable.
    stable_when_load_and_data_stable: assert property (
        @(posedge clk) disable iff (reset) (load && $stable(data)) |-> $stable(out)
    );

    // With load asserted and data changing, out changes accordingly.
    change_when_load_and_data_changes: assert property (
        @(posedge clk) disable iff (reset) (load && !$stable(data)) |-> !$stable(out)
    );
endmodule